import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpacesReach

/-!
# A write capability, atomic delivery, and attenuation as erasure

An actor holds some terms `K` fully and some names `W` write-only, after KLAIM's `out` right,
Rholang's `bundle+` and the output side of Pierce–Sangiorgi channel types. A write-only name
permits produce ports at its space and nothing else: no take, no read, no absence or count check.

* **Typing** (`WriteHolds`): the rule's take and read ports, tells and read-side spaces (take,
  read, absence, count) are terms of `K`; each produce port is a full port, with its space and
  placed term in `K`, or writes a payload of `K` at a written name of `W`.
* **Admission** (`WriteAdmits`, `WriteStep`): reach-relative selection with the reach of `K` alone.
  The read side resolves into that reach (`WriteAdmits.read_space_reached`); produce ports land in
  it or at a write-only name (`WriteAdmits.made_lands`).

## What is proved

* **Confinement** (`write_only_confinement`): for a write-only name `w` outside the holder's
  reach, its firings take, read and check nothing at `w`, resolve no read-side space there, and
  remove nothing there: what is at `w` after a firing is what was there and what the firing made.
  Validity does not depend on the occurrences at `w` (`writeAdmits_iff_of_agree`,
  `write_only_unobserved`), and `w` stays outside the holder's reach along its own steps
  (`write_reach_after_step`, `write_confined_along_run`).
* **Atomic delivery** (`WriteStep.makes_together`): one step makes all its outputs together. In
  `WriteControls` one firing makes the receipt in the payee's ledger and the settlement at the
  payer's own space (`payer_settles_atomically`), and no auditor can then see the settlement
  without the receipt (`no_gap_after_atomic`). The two-firing mailbox version, as in
  `forwarder_gap_observable`, shows the gap (`mailbox_gap_observable`).
* **Attenuation as erasure.** The typed holder does nothing the untyped full holder of the same
  names could not (`WriteAdmits.full`). For a rule whose read-side spaces are written names, the
  two are admitted exactly the same selections (`attenuation_is_erasure`): the restriction is a
  static property of the rule, checked at formation, and costs nothing at run time. For a rule that
  searches, the full holder's search finds the write-only space and the typed holder's does not
  (`full_search_reads_ledger`, `typed_search_refused_at_ledger`): there the write-only names are
  kept out of the reach that the search ranges over.

## Controls (`WriteControls`)

* Positive: the payer settles and publishes its receipt in the ledger atomically.
* Negative: a rule reading the ledger cannot be typed for the payer
  (`payer_cannot_type_ledger_read`); the payer's search is refused at the ledger although the
  candidate step would read there (`search_valid_at_ledger`, `typed_search_refused_at_ledger`);
  every admitted firing of the payer leaves the ledger's entry in place (`payer_confined`).
* Gap: the mailbox version lets an auditor see the settlement before the receipt arrives.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uN uO

/-! ## The read side and the typing -/

section ReadSide

variable {T : Type uT} {S : Type uS} {N : Type uN} {A : SubstitutionAction T S}

/-- The read side of a rule: the spaces of its take and read ports and of its absence and count
checks. -/
def LocatedRule.readSpaces (r : LocatedRule T) : List T :=
  r.take.map Prod.fst ++ r.read.map Prod.fst ++ r.checks.filterMap LocatedCheck.space?

theorem LocatedRule.mem_spaces_iff {r : LocatedRule T} {s : T} :
    s ∈ r.spaces ↔ s ∈ r.readSpaces ∨ s ∈ r.produce.map Prod.fst := by
  simp only [LocatedRule.spaces, LocatedRule.readSpaces, List.mem_append]
  tauto

theorem take_readSpace_mem {r : LocatedRule T} {port : T × T} (member : port ∈ r.take) :
    port.1 ∈ r.readSpaces :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨port, member, rfl⟩))

theorem read_readSpace_mem {r : LocatedRule T} {port : T × T} (member : port ∈ r.read) :
    port.1 ∈ r.readSpaces :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨port, member, rfl⟩))

theorem check_readSpace_mem {r : LocatedRule T} {check : LocatedCheck T}
    (member : check ∈ r.checks) {s : T} (space : check.space? = some s) : s ∈ r.readSpaces :=
  List.mem_append_right _ (List.mem_filterMap.mpr ⟨check, member, space⟩)

variable (sts : SpaceTerms A N)

/-- **A rule typed for an actor that holds `K` fully and the names `W` write-only.** -/
structure WriteHolds (r : LocatedRule T) (K : Set T) (W : Set N) : Prop where
  ports : ∀ p ∈ (r.toRule sts).take ++ (r.toRule sts).read, p ∈ K
  tells : ∀ e ∈ r.tell, e.1 ∈ K ∧ e.2 ∈ K
  readSpaces : ∀ s ∈ r.readSpaces, s ∈ K
  produce : ∀ port ∈ r.produce,
    (port.1 ∈ K ∧ place sts port ∈ K) ∨ ∃ w ∈ W, port.1 = sts.name w ∧ port.2 ∈ K

/-- The read side of the rule is written: every take, read, absence and count space is a name. -/
def ReadSideWritten (r : LocatedRule T) : Prop := ∀ s ∈ r.readSpaces, ∃ n, s = sts.name n

/-- **The untyped full holder** of the same names: `K`, each write-only name, and each placement
of a payload of `K` at one. -/
def fullHolder (K : Set T) (W : Set N) : Set T :=
  K ∪ {t | ∃ w ∈ W, t = sts.name w ∨ ∃ q ∈ K, t = sts.atSpace (sts.name w) q}

variable {sts}

/-- A typed rule is held by the full holder. -/
theorem WriteHolds.holdsRule {r : LocatedRule T} {K : Set T} {W : Set N}
    (holds : WriteHolds sts r K W) : HoldsRule (sts := sts) r (fullHolder sts K W) := by
  refine ⟨fun p member => Or.inl (holds.ports p member),
    fun e member => ⟨Or.inl (holds.tells e member).1, Or.inl (holds.tells e member).2⟩,
    fun p member => ?_, fun s member => ?_⟩
  · simp only [LocatedRule.toRule, List.mem_map] at member
    obtain ⟨port, portMember, rfl⟩ := member
    rcases holds.produce port portMember with ⟨_, placed⟩ | ⟨w, inW, named, inK⟩
    · exact Or.inl placed
    · refine Or.inr ⟨w, inW, Or.inr ⟨port.2, inK, ?_⟩⟩
      simp only [place, named]
  · rcases LocatedRule.mem_spaces_iff.mp member with readSide | produced
    · exact Or.inl (holds.readSpaces s readSide)
    · obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp produced
      rcases holds.produce port portMember with ⟨inK, _⟩ | ⟨w, inW, named, _⟩
      · exact Or.inl inK
      · exact Or.inr ⟨w, inW, Or.inl named⟩

end ReadSide

/-! ## Admission with write-only names -/

section Write

variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO} [DecidableEq N] [DecidableEq O]
  {A : SubstitutionAction T S} {sts : SpaceTerms A N} (ns : NameSwap sts)

/-- **Admission with write-only names.** The holder of `K` fully and `W` write-only may fire a
selection of a typed rule when the selection is valid for the candidate step, every occurrence it
takes or reads lies at a name `K` reaches, and the selection's own problem resolves every space
position of the rule. -/
structure WriteAdmits (K : Set T) (W : Set N) (space payload : O → T) (r : LocatedRule T)
    (C : Configuration T O) (selection : Selection O) : Prop where
  holds : WriteHolds sts r K W
  valid : selection.Valid A (located sts space payload) (r.toRule sts) C
  selected : ∀ o ∈ selection.taken ++ selection.read, AtReached ns K space payload C o
  resolved : ∀ s ∈ r.spaces,
    Resolves sts (selection.problem (located sts space payload) (r.toRule sts) C) s

/-- The step of a holder with write-only names: the candidate step on an admitted selection. -/
def WriteStep (K : Set T) (W : Set N) (space payload : O → T) (r : LocatedRule T)
    (before after : Configuration T O) : Prop :=
  ∃ selection, WriteAdmits ns K W space payload r before selection ∧
    after = selection.result (located sts space payload) (r.toRule sts) before

variable {ns}
variable {K : Set T} {W : Set N} {space payload : O → T} {r : LocatedRule T}
  {C : Configuration T O} {selection : Selection O}

theorem WriteStep.step {D : Configuration T O} (step : WriteStep ns K W space payload r C D) :
    Step A (located sts space payload) (r.toRule sts) C D := by
  obtain ⟨selection, admits, rfl⟩ := step
  exact ⟨selection, admits.valid, rfl⟩

/-- **The read side resolves into the holder's reach.** -/
theorem WriteAdmits.read_space_reached (admits : WriteAdmits ns K W space payload r C selection)
    {s : T} (member : s ∈ r.readSpaces) :
    ∃ k, Reached ns K space payload C k ∧
      ResolvesTo sts (selection.problem (located sts space payload) (r.toRule sts) C) s k := by
  obtain ⟨k, at_k⟩ := admits.resolved s (LocatedRule.mem_spaces_iff.mpr (Or.inl member))
  exact ⟨k, resolved_in_firing_reached_of admits.valid admits.holds.ports admits.holds.tells
    admits.selected (admits.holds.readSpaces s member) at_k, at_k⟩

omit [DecidableEq N] in
/-- A made occurrence is the placement of one of the rule's produce ports. -/
theorem made_placed (valid : selection.Valid A (located sts space payload) (r.toRule sts) C)
    {o : O} (made : o ∈ selection.made) :
    ∃ port ∈ r.produce, place sts port = located sts space payload o := by
  have output : located sts space payload o ∈ (r.toRule sts).produce := by
    rw [← valid.outputs]
    exact List.mem_map.mpr ⟨o, made, rfl⟩
  simp only [LocatedRule.toRule, List.mem_map] at output
  exact output

/-- **Produce ports land in the holder's reach or at a write-only name.** -/
theorem WriteAdmits.made_lands (admits : WriteAdmits ns K W space payload r C selection) {o : O}
    (made : o ∈ selection.made) :
    (∃ k, Reached ns K space payload C k ∧
      ResolvesTo sts (selection.problem (located sts space payload) (r.toRule sts) C)
        (space o) k) ∨ ∃ w ∈ W, space o = sts.name w := by
  obtain ⟨port, member, same, _⟩ := made_port admits.valid made
  rcases admits.holds.produce port member with ⟨inK, _⟩ | ⟨w, inW, named, _⟩
  · left
    obtain ⟨k, at_k⟩ := admits.resolved port.1 (produce_space_mem member)
    exact ⟨k, resolved_in_firing_reached_of admits.valid admits.holds.ports admits.holds.tells
      admits.selected inK at_k, same ▸ at_k⟩
  · exact Or.inr ⟨w, inW, same.symm.trans named⟩

/-- **Confinement.** For a write-only name `w` outside the holder's reach, a firing takes and
reads nothing at `w`, resolves no read-side space there, matches no check there, and removes
nothing there; what is present afterwards is what was present or what the firing made. -/
theorem write_only_confinement (admits : WriteAdmits ns K W space payload r C selection) {w : N}
    (unreached : ¬ Reached ns K space payload C w) :
    (∀ o ∈ selection.taken ++ selection.read, ¬ ResolvesTo sts C.equations (space o) w) ∧
      (∀ s ∈ r.readSpaces,
        ¬ ResolvesTo sts (selection.problem (located sts space payload) (r.toRule sts) C) s w) ∧
      (∀ s ∈ r.readSpaces, ∀ p : T, ∀ σ : S,
        A.Models σ (selection.problem (located sts space payload) (r.toRule sts) C) →
          ∀ o ∈ C.present, ResolvesTo sts C.equations (space o) w →
            ¬ A.E (A.apply σ (sts.atSpace s p)) (A.apply σ (located sts space payload o))) ∧
      (∀ o ∈ C.present, ResolvesTo sts C.equations (space o) w →
        o ∈ (selection.result (located sts space payload) (r.toRule sts) C).present) ∧
      ∀ o ∈ (selection.result (located sts space payload) (r.toRule sts) C).present,
        o ∈ C.present ∨ o ∈ selection.made := by
  have consistentBefore : A.Consistent C.equations := valid_before_consistent admits.valid
  have notTouched : ∀ o ∈ selection.taken ++ selection.read,
      ¬ ResolvesTo sts C.equations (space o) w := by
    intro o member at_w
    obtain ⟨k, reached, at_k⟩ := admits.selected o member
    have names : w = k := ResolvesTo.unique consistentBefore at_w at_k
    exact unreached (names ▸ reached)
  refine ⟨notTouched, fun s member at_w => ?_, fun s member p σ solved o present at_w matching => ?_,
    fun o present at_w => ?_, fun o after => ?_⟩
  · obtain ⟨k, reached, at_k⟩ := admits.read_space_reached member
    have names : w = k := ResolvesTo.unique admits.valid.consistent at_w at_k
    exact unreached (names ▸ reached)
  · obtain ⟨k, reached, at_k⟩ := admits.read_space_reached member
    simp only [located, sts.apply_atSpace, sts.E_atSpace] at matching
    have lifted : ResolvesTo sts (selection.problem (located sts space payload) (r.toRule sts) C)
        (space o) w := ResolvesTo.of_refines admits.valid.refines at_w
    have names : k = w := at_k.name_eq solved lifted matching.1
    exact unreached (names ▸ reached)
  · apply mem_fire.mpr
    left
    refine ⟨present, fun takenMember => notTouched o ?_ at_w⟩
    exact List.mem_append_left _ (by simpa [Selection.commit] using takenMember)
  · rcases mem_fire.mp after with ⟨old, _⟩ | madeMember
    · exact Or.inl old
    · exact Or.inr (by simpa [Selection.commit] using madeMember)

/-- **Atomic delivery.** One step of the holder makes every produced occurrence together: each is
absent before the step and present after it, at the full space or the write-only name its port
names. No configuration lies between. -/
theorem WriteStep.makes_together {D : Configuration T O}
    (step : WriteStep ns K W space payload r C D) :
    ∃ selection : Selection O,
      D = selection.result (located sts space payload) (r.toRule sts) C ∧
      ∀ o ∈ selection.made, o ∉ C.present ∧ o ∈ D.present ∧
        ((∃ k, Reached ns K space payload C k ∧ ResolvesTo sts D.equations (space o) k) ∨
          ∃ w ∈ W, space o = sts.name w) := by
  obtain ⟨selection, admits, rfl⟩ := step
  refine ⟨selection, rfl, fun o made => ⟨?_, ?_, admits.made_lands made⟩⟩
  · exact fun present => Finset.disjoint_left.mp admits.valid.occurrences.fresh
      (by simpa [Selection.commit] using made) present
  · exact mem_fire.mpr (Or.inr (by simpa [Selection.commit] using made))

/-- One direction of locality for the write holder. -/
theorem WriteAdmits.of_agree {D : Configuration T O}
    (admits : WriteAdmits ns K W space payload r C selection)
    (agree : AgreeOnReach ns K space payload C D) (wellC : WellLocated sts space C)
    (wellD : WellLocated sts space D) (fresh : Disjoint selection.made.toFinset D.present) :
    WriteAdmits ns K W space payload r D selection := by
  refine ⟨admits.holds, valid_of_agree_on_reach admits.valid admits.selected
    (fun s member => admits.read_space_reached (List.mem_append_right _ member)) agree wellC wellD
      fresh,
    fun o member => ?_, ?_⟩
  · obtain ⟨k, reached, at_k⟩ := admits.selected o member
    refine ⟨k, (agree.reached_iff k).mp reached, ?_⟩
    rw [← agree.1]
    exact at_k
  · have problems : selection.problem (located sts space payload) (r.toRule sts) D =
        selection.problem (located sts space payload) (r.toRule sts) C := by
      simp only [Selection.problem, agree.1]
    rw [problems]
    exact admits.resolved

/-- **No observation through a write-only name**: validity depends only on the store and the
occurrences in the holder's reach. -/
theorem writeAdmits_iff_of_agree {D : Configuration T O}
    (agree : AgreeOnReach ns K space payload C D) (wellC : WellLocated sts space C)
    (wellD : WellLocated sts space D) (freshC : Disjoint selection.made.toFinset C.present)
    (freshD : Disjoint selection.made.toFinset D.present) :
    WriteAdmits ns K W space payload r C selection ↔
      WriteAdmits ns K W space payload r D selection :=
  ⟨fun admits => admits.of_agree agree wellC wellD freshD,
    fun admits => admits.of_agree agree.symm wellD wellC freshC⟩

/-- Two configurations with one consistent store that differ only at an unreached write-only name
admit the same selections of the holder. -/
theorem write_only_unobserved {D : Configuration T O} {w : N}
    (consistent : A.Consistent C.equations) (sameStore : C.equations = D.equations)
    (elsewhere : ∀ o, ¬ ResolvesTo sts C.equations (space o) w → (o ∈ C.present ↔ o ∈ D.present))
    (unreached : ¬ Reached ns K space payload C w) (wellC : WellLocated sts space C)
    (wellD : WellLocated sts space D) (freshC : Disjoint selection.made.toFinset C.present)
    (freshD : Disjoint selection.made.toFinset D.present) :
    WriteAdmits ns K W space payload r C selection ↔
      WriteAdmits ns K W space payload r D selection := by
  refine writeAdmits_iff_of_agree ⟨sameStore, ?_⟩ wellC wellD freshC freshD
  rintro o ⟨k, reached, at_k⟩
  apply elsewhere o
  intro at_w
  have names : w = k := ResolvesTo.unique consistent at_w at_k
  exact unreached (names ▸ reached)

/-- **The write-only names stay outside the holder's reach along its own steps.** -/
theorem write_reach_after_step {D : Configuration T O}
    (step : WriteStep ns K W space payload r C D) (wellLocated : WellLocated sts space C)
    (outside : ∀ w ∈ W, ¬ Reached ns K space payload C w) {n : N}
    (reached : Reached ns K space payload D n) : Reached ns K space payload C n := by
  obtain ⟨selection, admits, rfl⟩ := step
  apply reached (Reached ns K space payload C)
  intro m possessedAfter
  have labelsAfter : labelsAt sts
      (selection.result (located sts space payload) (r.toRule sts) C).equations space
      (located sts space payload)
      (selection.result (located sts space payload) (r.toRule sts) C).present
      (Reached ns K space payload C) ⊆
      K ∪ labelsAt sts C.equations space (located sts space payload) C.present
        (Reached ns K space payload C) := by
    rintro t ⟨o, presentAfter, k, inR, at_k, rfl⟩
    rcases mem_fire.mp presentAfter with ⟨old, _⟩ | madeMember
    · obtain ⟨k', at_k'⟩ := wellLocated o old
      have names : k = k' := ResolvesTo.unique admits.valid.consistent at_k
        (ResolvesTo.of_refines admits.valid.refines at_k')
      subst names
      exact Or.inr ⟨o, old, k, inR, at_k', rfl⟩
    · have made : o ∈ selection.made := by simpa [Selection.commit] using madeMember
      obtain ⟨port, member, same⟩ := made_placed admits.valid made
      rcases admits.holds.produce port member with ⟨_, placed⟩ | ⟨w, inW, named, _⟩
      · exact Or.inl (same ▸ placed)
      · exfalso
        have spaceOf : space o = sts.name w := by
          obtain ⟨spaces, _⟩ := sts.atSpace_injective _ _ _ _ same
          exact spaces.symm.trans named
        have names : k = w := ResolvesTo.unique admits.valid.consistent at_k
          (spaceOf ▸ resolvesTo_name _ w)
        exact outside w inW (names ▸ inR)
  have widened := possessedAfter.mono (Set.union_subset Set.subset_union_left labelsAfter)
  have possessedBefore := possession_after_step admits.valid
    (fun p member => Or.inl (admits.holds.ports p member))
    (fun e member => ⟨Or.inl (admits.holds.tells e member).1,
      Or.inl (admits.holds.tells e member).2⟩)
    (fun o member => Or.inr ⟨o, by
      rcases List.mem_append.mp member with taken | read
      · exact admits.valid.occurrences.taken_subset (by simpa [Selection.commit] using taken)
      · exact admits.valid.occurrences.kept_subset (by simpa [Selection.commit] using read),
      (admits.selected o member).choose, (admits.selected o member).choose_spec.1,
      (admits.selected o member).choose_spec.2, rfl⟩) widened
  exact Reach.closed possessedBefore

/-- The step of a holder with write-only names keeps configurations well located. -/
theorem WriteStep.wellLocated {D : Configuration T O} (step : WriteStep ns K W space payload r C D)
    (wellLocated : WellLocated sts space C) : WellLocated sts space D := by
  obtain ⟨selection, admits, rfl⟩ := step
  intro o present
  rcases mem_fire.mp present with ⟨old, _⟩ | madeMember
  · obtain ⟨n, at_n⟩ := wellLocated o old
    exact ⟨n, ResolvesTo.of_refines admits.valid.refines at_n⟩
  · have made : o ∈ selection.made := by simpa [Selection.commit] using madeMember
    rcases admits.made_lands made with ⟨k, _, at_k⟩ | ⟨w, _, named⟩
    · exact ⟨k, at_k⟩
    · exact ⟨w, named ▸ resolvesTo_name _ w⟩

variable (ns) in
/-- A run of steps of one holder with write-only names. -/
inductive WriteRun (K : Set T) (W : Set N) (space payload : O → T) :
    Configuration T O → List (LocatedRule T) → Configuration T O → Prop
  | nil (C : Configuration T O) : WriteRun K W space payload C [] C
  | cons {C D E : Configuration T O} {r : LocatedRule T} {rest : List (LocatedRule T)} :
      WriteStep ns K W space payload r C D → WriteRun K W space payload D rest E →
        WriteRun K W space payload C (r :: rest) E

/-- **Confinement along a run**: from a well-located configuration in which the holder reaches no
write-only name, it reaches none at any later configuration of its own run. -/
theorem write_confined_along_run {E : Configuration T O} {rules : List (LocatedRule T)}
    (run : WriteRun ns K W space payload C rules E) (wellLocated : WellLocated sts space C)
    (outside : ∀ w ∈ W, ¬ Reached ns K space payload C w) :
    ∀ w ∈ W, ¬ Reached ns K space payload E w := by
  induction run with
  | nil => exact outside
  | cons step _ ih =>
      apply ih (step.wellLocated wellLocated)
      intro w inW reached
      exact outside w inW (write_reach_after_step step wellLocated outside reached)

/-! ### Attenuation as erasure -/

/-- **The typed holder does nothing the untyped full holder could not.** -/
theorem WriteAdmits.full (admits : WriteAdmits ns K W space payload r C selection) :
    ReachAdmits ns (fullHolder sts K W) space payload r C selection :=
  ⟨admits.holds.holdsRule, admits.valid,
    fun o member => by
      obtain ⟨k, reached, at_k⟩ := admits.selected o member
      exact ⟨k, reached.mono Set.subset_union_left, at_k⟩,
    admits.resolved⟩

omit [DecidableEq N] in
/-- Each selected occurrence is equated, in the selection's problem, with the placement of one of
the rule's take or read ports. -/
theorem selected_port (valid : selection.Valid A (located sts space payload) (r.toRule sts) C)
    {o : O} (member : o ∈ selection.taken ++ selection.read) :
    ∃ port ∈ r.take ++ r.read, (place sts port, located sts space payload o) ∈
      selection.problem (located sts space payload) (r.toRule sts) C := by
  rcases List.mem_append.mp member with taken | read
  · obtain ⟨p, pMember, pair⟩ := mem_equations_of_mem_right (located sts space payload)
      valid.take_length taken
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp pMember
    refine ⟨port, List.mem_append_left _ portMember, ?_⟩
    simp only [Selection.problem, List.mem_append]
    exact Or.inl (Or.inl (Or.inr pair))
  · obtain ⟨p, pMember, pair⟩ := mem_equations_of_mem_right (located sts space payload)
      valid.read_length read
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp pMember
    refine ⟨port, List.mem_append_right _ portMember, ?_⟩
    simp only [Selection.problem, List.mem_append]
    exact Or.inl (Or.inr pair)

/-- **Attenuation as erasure.** For a typed rule whose read side is written, the holder of `W`
write-only is admitted exactly the selections the untyped full holder of the same names is
admitted. The write-only restriction is a static property of the rule, checked at formation, and
the run-time admission is the same. -/
theorem attenuation_is_erasure (holds : WriteHolds sts r K W) (written : ReadSideWritten sts r)
    (wellLocated : WellLocated sts space C) (consistent : A.Consistent C.equations) :
    WriteAdmits ns K W space payload r C selection ↔
      ReachAdmits ns (fullHolder sts K W) space payload r C selection := by
  refine ⟨WriteAdmits.full, fun admits => ⟨holds, admits.valid, fun o member => ?_,
    admits.resolved⟩⟩
  obtain ⟨port, portMember, pair⟩ := selected_port admits.valid member
  have readSide : port.1 ∈ r.readSpaces := by
    rcases List.mem_append.mp portMember with takeMember | readMember
    · exact take_readSpace_mem takeMember
    · exact read_readSpace_mem readMember
  obtain ⟨m, named⟩ := written port.1 readSide
  have inK : sts.name m ∈ K := named ▸ holds.readSpaces port.1 readSide
  have present : o ∈ C.present := by
    rcases List.mem_append.mp member with taken | read
    · exact admits.valid.occurrences.taken_subset (by simpa [Selection.commit] using taken)
    · exact admits.valid.occurrences.kept_subset (by simpa [Selection.commit] using read)
  obtain ⟨m', at_m'⟩ := wellLocated o present
  obtain ⟨σ, solved⟩ := admits.valid.consistent
  have same := solved _ pair
  simp only [SubstitutionAction.Solves, place, located, sts.apply_atSpace, sts.E_atSpace, named,
    sts.apply_name] at same
  have names : m = m' := (sts.E_name m m').mp
    (A.equivalence.trans same.1 (ResolvesTo.of_refines admits.valid.refines at_m' σ solved))
  subst names
  exact ⟨m, Reach.of_possesses (written_name_possessed consistent inK), at_m'⟩

end Write

/-! ## Controls: a payer, a payee's ledger and an auditor -/

namespace WriteControls

open Controls

def invoice (n : Tm) : Tm := .app (.sym "invoice") n
def settledOf (n : Tm) : Tm := .app (.sym "settled") n
def receipt (n : Tm) : Tm := .app (.sym "receipt") n
def n42 : Tm := .sym "n42"

/-- Spaces: 1 the payer's own, 4 the payer's outbox, 5 the payee's ledger, 6 the auditor's alarms.
Occurrences: 0 the invoice at 1; 1 an old entry in the ledger; 2 the settlement at 1; 3 the
receipt in the ledger; 4 the receipt in the outbox; 9 an alarm. -/
def paySpace : Nat → Tm
  | 0 => .nm 1
  | 1 => .nm 5
  | 2 => .nm 1
  | 3 => .nm 5
  | 4 => .nm 4
  | _ => .nm 6

def payPayload : Nat → Tm
  | 0 => invoice n42
  | 1 => .sym "old"
  | 2 => settledOf (.var 0)
  | 3 => receipt (.var 0)
  | 4 => receipt (.var 0)
  | _ => .sym "alarm"

def payWorld : Configuration Tm Nat := ⟨[], {0, 1}⟩

theorem payWorld_wellLocated : WellLocated spaces paySpace payWorld := by
  intro o present
  simp only [payWorld, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · exact ⟨1, resolvesTo_name _ 1⟩
  · exact ⟨5, resolvesTo_name _ 5⟩

/-- **The payer's settlement**: take the invoice at its own space, publish the settlement there and
the receipt in the payee's ledger, in one firing. -/
def settle : LocatedRule Tm :=
  ⟨[(.nm 1, invoice (.var 0))], [], [], [],
    [(.nm 1, settledOf (.var 0)), (.nm 5, receipt (.var 0))]⟩

/-- The payer holds its own space fully. -/
def payer : Set Tm :=
  {.nm 1, .loc (.nm 1) (invoice (.var 0)), .loc (.nm 1) (settledOf (.var 0)), receipt (.var 0)}

/-- It holds the payee's ledger write-only. -/
def ledger : Set Nat := {5}

def settleSel : Selection Nat := ⟨[0], [], [2, 3]⟩

def settledWorld : Configuration Tm Nat :=
  settleSel.result (located spaces paySpace payPayload) (settle.toRule spaces) payWorld

theorem payer_holds : WriteHolds spaces settle payer ledger := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [settle, LocatedRule.toRule, place, payer, spaces]
  · simp [settle]
  · simp [LocatedRule.readSpaces, settle, payer]
  · intro port member
    simp only [settle, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Or.inl ⟨by simp [payer], by simp [payer, place, spaces]⟩
    · exact Or.inr ⟨5, by simp [ledger], rfl, by simp [payer]⟩

theorem payer_names : ∀ t ∈ payer, ∀ j ∈ t.namesIn, j < 2 := by
  intro t member j named
  simp only [payer, Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals simp [Tm.namesIn, invoice, settledOf, receipt] at named
  all_goals omega

theorem pay_labels_below : ∀ o ∈ payWorld.present, ∀ k, k < 2 →
    ResolvesTo spaces payWorld.equations (paySpace o) k →
      ∀ j ∈ (located spaces paySpace payPayload o).namesIn, j < 2 := by
  intro o present k below at_k j named
  simp only [payWorld, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · simp [located, spaces, paySpace, payPayload, invoice, n42, Tm.namesIn] at named
    omega
  · have := (resolvesTo_nm_nil (j := 5) (k := k)).mp at_k
    omega

/-- A holder whose full terms write only the name 1 does not reach the ledger. -/
theorem ledger_unreached {K : Set Tm} (bounded : ∀ t ∈ K, ∀ j ∈ t.namesIn, j < 2) :
    ¬ Reached names K paySpace payPayload payWorld 5 := fun reached => by
  have := reach_below 2 (by norm_num) bounded pay_labels_below (by simp [payWorld]) reached
  omega

theorem settle_valid :
    settleSel.Valid action (located spaces paySpace payPayload) (settle.toRule spaces) payWorld := by
  refine ⟨by simp [settleSel], by simp [settleSel], rfl, rfl, rfl,
    ⟨by simp [Selection.commit, settleSel, payWorld], by simp [Selection.commit, settleSel],
      by simp [Selection.commit, settleSel],
      by simp [Selection.commit, settleSel, payWorld, Finset.disjoint_left],
      by simp [Selection.commit]⟩,
    ⟨fun _ => n42, ?_⟩, by simp [settle, LocatedRule.toRule]⟩
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, settle,
    LocatedRule.toRule, settleSel, payWorld, place, located, spaces, paySpace, payPayload, invoice,
    n42, Tm.subst]

theorem settle_admits :
    WriteAdmits names payer ledger paySpace payPayload settle payWorld settleSel := by
  refine ⟨payer_holds, settle_valid, ?_, ?_⟩
  · intro o member
    simp only [settleSel, List.append_nil, List.mem_singleton] at member
    subst member
    exact ⟨1, Reach.of_possesses (written_name_possessed ⟨Tm.var, by simp [payWorld]⟩
      (by simp [payer, spaces])), resolvesTo_name _ 1⟩
  · intro s member
    simp only [LocatedRule.spaces, settle, List.map_cons, List.map_nil, List.filterMap_nil,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨1, resolvesTo_name _ 1⟩
    · exact ⟨1, resolvesTo_name _ 1⟩
    · exact ⟨5, resolvesTo_name _ 5⟩

/-- **Positive control: atomic delivery.** In one firing the payer takes its invoice, settles at
its own space and publishes the receipt in the payee's ledger: both occurrences are absent before
the step and present after it. -/
theorem payer_settles_atomically :
    WriteStep names payer ledger paySpace payPayload settle payWorld settledWorld ∧
      2 ∉ payWorld.present ∧ 3 ∉ payWorld.present ∧
      2 ∈ settledWorld.present ∧ 3 ∈ settledWorld.present ∧
      paySpace 2 = .nm 1 ∧ paySpace 3 = .nm 5 := by
  refine ⟨⟨settleSel, settle_admits, rfl⟩, by simp [payWorld], by simp [payWorld], ?_, ?_, rfl, rfl⟩
  · simp [settledWorld, Selection.result, fire, Selection.commit, settleSel]
  · simp [settledWorld, Selection.result, fire, Selection.commit, settleSel]

/-- An auditor: having seen a settlement at the payer's space, raise an alarm if its receipt is not
in the ledger. -/
def audit : LocatedRule Tm :=
  ⟨[], [(.nm 1, settledOf (.var 7))], [], [.absent (.nm 5) (receipt (.var 7))],
    [(.nm 6, .sym "alarm")]⟩

theorem settledWorld_present : settledWorld.present = {1, 2, 3} := by
  ext x
  simp only [settledWorld, Selection.result, fire, Selection.commit, settleSel, payWorld,
    List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_singleton, Finset.mem_insert]
  omega

/-- **No gap**: after the atomic settlement no selection of the auditor is valid. -/
theorem no_gap_after_atomic (selection : Selection Nat) :
    ¬ selection.Valid action (located spaces paySpace payPayload) (audit.toRule spaces)
      settledWorld := by
  intro valid
  obtain ⟨σ, solved⟩ := valid.consistent
  have readLength : selection.read.length = 1 := by
    simpa [audit, LocatedRule.toRule] using valid.read_length.symm
  obtain ⟨o, chosen⟩ := List.length_eq_one_iff.mp readLength
  have reads := (Selection.models_problem action valid solved).2.2.1
  rw [chosen] at reads
  have first : (Tm.loc (.nm 1) (settledOf (.var 7))).subst σ =
      Tm.loc ((paySpace o).subst σ) ((payPayload o).subst σ) := (List.forall₂_cons.mp reads).1
  have present : o ∈ settledWorld.present :=
    valid.occurrences.kept_subset (by simp [Selection.commit, chosen])
  have holds := valid.checks (.absent (spaces.atSpace (.nm 5) (receipt (.var 7))))
    (by simp [audit, LocatedRule.toRule, LocatedCheck.toCheck]) σ solved
  rw [settledWorld_present] at present
  simp only [Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl | rfl
  · simp [paySpace, payPayload, settledOf, Tm.subst] at first
  · apply holds 3 (by rw [settledWorld_present]; simp)
    simp [paySpace, payPayload, settledOf, receipt, spaces, located, Tm.subst] at first ⊢
    exact first
  · simp [paySpace, payPayload, settledOf, Tm.subst] at first

/-! ### The two-firing mailbox version -/

/-- The payer settles and leaves the receipt in its outbox 4, for the ledger owner's forwarder. -/
def settleToOutbox : LocatedRule Tm :=
  ⟨[(.nm 1, invoice (.var 0))], [], [], [],
    [(.nm 1, settledOf (.var 0)), (.nm 4, receipt (.var 0))]⟩

def outboxSel : Selection Nat := ⟨[0], [], [2, 4]⟩

def outboxWorld : Configuration Tm Nat :=
  outboxSel.result (located spaces paySpace payPayload) (settleToOutbox.toRule spaces) payWorld

theorem outboxWorld_present : outboxWorld.present = {1, 2, 4} := by
  ext x
  simp only [outboxWorld, Selection.result, fire, Selection.commit, outboxSel, payWorld,
    List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_singleton, Finset.mem_insert]
  omega

def auditSel : Selection Nat := ⟨[], [2], [9]⟩

/-- **The gap of the two-firing version**: after the payer's firing, before the forwarder's, the
auditor sees the settlement while the ledger lacks the receipt. -/
theorem mailbox_gap_observable :
    outboxSel.Valid action (located spaces paySpace payPayload) (settleToOutbox.toRule spaces)
        payWorld ∧
      auditSel.Valid action (located spaces paySpace payPayload) (audit.toRule spaces)
        outboxWorld := by
  constructor
  · refine ⟨by simp [outboxSel], by simp [outboxSel], rfl, rfl, rfl,
      ⟨by simp [Selection.commit, outboxSel, payWorld], by simp [Selection.commit, outboxSel],
        by simp [Selection.commit, outboxSel],
        by simp [Selection.commit, outboxSel, payWorld, Finset.disjoint_left],
        by simp [Selection.commit]⟩,
      ⟨fun _ => n42, ?_⟩, by simp [settleToOutbox, LocatedRule.toRule]⟩
    simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, settleToOutbox,
      LocatedRule.toRule, outboxSel, payWorld, place, located, spaces, paySpace, payPayload,
      invoice, n42, Tm.subst]
  · refine ⟨by simp [auditSel], by simp [auditSel], rfl, rfl, rfl,
      ⟨by simp [Selection.commit, auditSel], ?_, by simp [Selection.commit, auditSel], ?_,
        by simp [Selection.commit]⟩, ⟨fun _ => n42, ?_⟩, ?_⟩
    · intro o member
      simp only [Selection.commit, auditSel, List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq, Finset.mem_singleton] at member
      subst member
      rw [outboxWorld_present]
      simp
    · rw [outboxWorld_present]
      simp [Selection.commit, auditSel]
    · simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, audit,
        LocatedRule.toRule, auditSel, outboxWorld, Selection.result, outboxSel, settleToOutbox,
        payWorld, place, located, spaces, paySpace, payPayload, invoice, settledOf, n42, Tm.subst]
    · intro check member σ _
      simp only [audit, LocatedRule.toRule, LocatedCheck.toCheck, List.map_cons, List.map_nil,
        List.mem_singleton] at member
      subst member
      intro o present
      rw [outboxWorld_present] at present
      simp only [Finset.mem_insert, Finset.mem_singleton] at present
      rcases present with rfl | rfl | rfl <;>
        simp [spaces, located, paySpace, payPayload, receipt, settledOf, Tm.subst]

/-! ### Negative controls -/

/-- A rule that reads the ledger. -/
def peekLedger : LocatedRule Tm := ⟨[], [(.nm 5, .var 9)], [], [], []⟩

/-- **By formation**: a holder whose full terms do not write the ledger's name cannot type a rule
that reads the ledger. -/
theorem payer_cannot_type_ledger_read {K : Set Tm} (notWritten : Tm.nm 5 ∉ K) :
    ¬ WriteHolds spaces peekLedger K ledger :=
  fun holds => notWritten (holds.readSpaces (.nm 5) (by simp [LocatedRule.readSpaces, peekLedger]))

/-- A search: read any row at any space. -/
def searchAny : LocatedRule Tm := ⟨[], [(.var 9, .var 10)], [], [], []⟩

/-- The payer with the terms of the search. -/
def searchingPayer : Set Tm := payer ∪ {.var 9, .loc (.var 9) (.var 10)}

def readLedgerSel : Selection Nat := ⟨[], [1], []⟩

theorem searchAny_holds : WriteHolds spaces searchAny searchingPayer ledger := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [searchAny, LocatedRule.toRule, LocatedRule.readSpaces, place, searchingPayer, spaces]

theorem searchingPayer_names : ∀ t ∈ searchingPayer, ∀ j ∈ t.namesIn, j < 2 := by
  rintro t (member | member) j named
  · exact payer_names t member j named
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
    rcases member with rfl | rfl <;> simp [Tm.namesIn] at named

/-- The candidate step would read the ledger's entry. -/
theorem search_valid_at_ledger :
    readLedgerSel.Valid action (located spaces paySpace payPayload) (searchAny.toRule spaces)
      payWorld := by
  refine ⟨by simp [readLedgerSel], by simp [readLedgerSel], rfl, rfl, rfl,
    ⟨by simp [Selection.commit, readLedgerSel], by simp [Selection.commit, readLedgerSel, payWorld],
      by simp [Selection.commit, readLedgerSel], by simp [Selection.commit, readLedgerSel],
      by simp [Selection.commit]⟩,
    ⟨fun i => if i = 9 then .nm 5 else .sym "old", ?_⟩, by simp [searchAny, LocatedRule.toRule]⟩
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, searchAny,
    LocatedRule.toRule, readLedgerSel, payWorld, place, located, spaces, paySpace, payPayload,
    Tm.subst]

/-- **Negative control: the typed payer's search is refused at the ledger.** -/
theorem typed_search_refused_at_ledger :
    ¬ WriteAdmits names searchingPayer ledger paySpace payPayload searchAny payWorld
      readLedgerSel := by
  intro admits
  obtain ⟨k, reached, at_k⟩ := admits.selected 1 (by simp [readLedgerSel])
  have named := (resolvesTo_nm_nil (j := 5) (k := k)).mp at_k
  subst named
  exact ledger_unreached searchingPayer_names reached

/-- **The untyped full holder's search reads the ledger**: for a searching rule the write-only
restriction is the exclusion of the ledger from the reach the search ranges over. -/
theorem full_search_reads_ledger :
    ReachAdmits names (fullHolder spaces searchingPayer ledger) paySpace payPayload searchAny
      payWorld readLedgerSel := by
  refine ⟨searchAny_holds.holdsRule, search_valid_at_ledger, ?_, ?_⟩
  · intro o member
    simp only [readLedgerSel, List.nil_append, List.mem_singleton] at member
    subst member
    exact ⟨5, Reach.of_possesses (written_name_possessed ⟨Tm.var, by simp [payWorld]⟩
      (Or.inr ⟨5, by simp [ledger], Or.inl rfl⟩)), resolvesTo_name _ 5⟩
  · intro s member
    simp only [LocatedRule.spaces, searchAny, List.map_cons, List.map_nil, List.filterMap_nil,
      List.nil_append, List.append_nil, List.mem_singleton] at member
    subst member
    refine ⟨5, fun σ solved => ?_⟩
    simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, searchAny,
      LocatedRule.toRule, readLedgerSel, payWorld, place, located, spaces, paySpace, payPayload,
      Tm.subst] at solved
    simpa [spaces, Tm.subst] using solved.1

/-- **Confinement in the payer world**: every admitted firing of the payer, of any rule, leaves the
ledger's entry in place. -/
theorem payer_confined (r : LocatedRule Tm) (selection : Selection Nat)
    (admits : WriteAdmits names payer ledger paySpace payPayload r payWorld selection) :
    1 ∈ (selection.result (located spaces paySpace payPayload) (r.toRule spaces)
      payWorld).present :=
  (write_only_confinement admits (ledger_unreached payer_names)).2.2.2.1 1 (by simp [payWorld])
    (resolvesTo_name _ 5)

/-! ### Erasure for the payer's settlement -/

theorem settle_read_written : ReadSideWritten spaces settle := by
  intro s member
  simp only [LocatedRule.readSpaces, settle, List.map_cons, List.map_nil, List.filterMap_nil,
    List.append_nil, List.mem_singleton] at member
  exact ⟨1, member⟩

/-- **Attenuation as erasure, on the payer**: the payer holding the ledger write-only is admitted
exactly what the full holder of the ledger is admitted for its settlement. -/
theorem settle_erasure (selection : Selection Nat) :
    WriteAdmits names payer ledger paySpace payPayload settle payWorld selection ↔
      ReachAdmits names (fullHolder spaces payer ledger) paySpace payPayload settle payWorld
        selection :=
  attenuation_is_erasure payer_holds settle_read_written payWorld_wellLocated
    ⟨Tm.var, by simp [payWorld]⟩

end WriteControls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

/-! ## Axiom audit -/

section Audit

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

#print axioms LocatedRule.mem_spaces_iff
#print axioms take_readSpace_mem
#print axioms read_readSpace_mem
#print axioms check_readSpace_mem
#print axioms WriteHolds.holdsRule
#print axioms WriteStep.step
#print axioms WriteAdmits.read_space_reached
#print axioms made_placed
#print axioms WriteAdmits.made_lands
#print axioms write_only_confinement
#print axioms WriteStep.makes_together
#print axioms WriteAdmits.of_agree
#print axioms writeAdmits_iff_of_agree
#print axioms write_only_unobserved
#print axioms write_reach_after_step
#print axioms WriteStep.wellLocated
#print axioms write_confined_along_run
#print axioms WriteAdmits.full
#print axioms selected_port
#print axioms attenuation_is_erasure
#print axioms WriteControls.payWorld_wellLocated
#print axioms WriteControls.payer_holds
#print axioms WriteControls.payer_names
#print axioms WriteControls.pay_labels_below
#print axioms WriteControls.ledger_unreached
#print axioms WriteControls.settle_valid
#print axioms WriteControls.settle_admits
#print axioms WriteControls.payer_settles_atomically
#print axioms WriteControls.settledWorld_present
#print axioms WriteControls.no_gap_after_atomic
#print axioms WriteControls.outboxWorld_present
#print axioms WriteControls.mailbox_gap_observable
#print axioms WriteControls.payer_cannot_type_ledger_read
#print axioms WriteControls.searchAny_holds
#print axioms WriteControls.searchingPayer_names
#print axioms WriteControls.search_valid_at_ledger
#print axioms WriteControls.typed_search_refused_at_ledger
#print axioms WriteControls.full_search_reads_ledger
#print axioms WriteControls.payer_confined
#print axioms WriteControls.settle_read_written
#print axioms WriteControls.settle_erasure

end Audit
