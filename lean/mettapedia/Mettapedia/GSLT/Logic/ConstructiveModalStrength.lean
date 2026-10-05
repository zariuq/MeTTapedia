import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

/-!
# A logical strength consequence of unrestricted modal reflection

The stream probes below are actual GSLTs with two roots, each having a
finite successor set. One root additionally reaches the zero stream. For a
binary sequence with at most one true entry, every finite modal observation
of that extra successor is already realized by one of the original streams.

Matching the extra successor by a bisimulation requires a single original
stream agreeing at every depth. The resulting disjunction is LLPO. Thus the
unrestricted image-finite Hennessy--Milner reflection principle has this
explicit logical consequence. No omniscience principle or reflection theorem
is assumed in the construction or in finite modal agreement itself.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ConstructiveModalStrength

open HennessyMilner

inductive Track where
  | even
  | odd
  | zero
  deriving DecidableEq

inductive State where
  | root (extra : Bool)
  | trace (track : Track) (position : Nat)
  deriving DecidableEq

def successors : State → List State
  | .root false => [.trace .even 0, .trace .odd 0]
  | .root true => [.trace .even 0, .trace .odd 0, .trace .zero 0]
  | .trace track position => [.trace track (position + 1)]

def reduction (source target : State) : Prop := target ∈ successors source

@[implicit_reducible] def theory : GSLT where
  Term := State
  equations := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  rewrites := reduction
  rewrites_resp_left := by
    intro left right target same reduces
    exact ⟨target, same ▸ reduces, rfl⟩
  rewrites_resp_right := by
    intro source target other reduces same
    exact same ▸ reduces

def bit (stream : Nat → Bool) : Track → Nat → Bool
  | .even, position => stream (2 * position)
  | .odd, position => stream (2 * position + 1)
  | .zero, _ => false

def observedBit (stream : Nat → Bool) : State → Bool
  | .root _ => false
  | .trace track position => bit stream track position

def system (stream : Nat → Bool) : System theory where
  Atom := Bool
  Label := PUnit
  observes atom state := atom = observedBit stream state
  observes_resp := by
    intro atom left right same
    exact same ▸ Iff.rfl
  act _ := reduction
  act_resp_left := by
    intro label left right target same reduces
    exact ⟨target, same ▸ reduces, rfl⟩
  act_resp_right := by
    intro label source target other reduces same
    exact same ▸ reduces

/-- Finiteness has an actual authored successor list at every state. -/
theorem successors_nodup (source : State) : (successors source).Nodup := by
  cases source with
  | root extra => cases extra <;> simp [successors]
  | trace track position => simp [successors]

/-- Both enumeration directions are computed from the authored list. -/
def successorIndices (source : State) :
    {target : State // target ∈ successors source} ≃ Fin (successors source).length where
  toFun target := ⟨(successors source).idxOf target.val, List.idxOf_lt_length_of_mem target.property⟩
  invFun index := ⟨(successors source).get index, List.get_mem _ _⟩
  left_inv target := Subtype.ext (List.idxOf_get (List.idxOf_lt_length_of_mem target.property))
  right_inv index := Fin.ext (List.get_idxOf (successors_nodup source) index)

/-- The finite cover is certified by its computed list index equivalence.
This avoids choosing a finite enumeration from a proposition of finiteness. -/
theorem imageFinite (stream : Nat → Bool) : (system stream).ImageFiniteModulo := by
  intro label source
  let : DecidableEq theory.Term := inferInstanceAs (DecidableEq State)
  refine ⟨{target | target ∈ successors source}, ?_, ?_⟩
  · exact Finite.intro (successorIndices source)
  intro target reduces
  exact ⟨target, reduces, rfl⟩

def lookahead : Formula Bool PUnit → Nat
  | .top => 0
  | .atom _ => 1
  | .conj first second => max (lookahead first) (lookahead second)
  | .neg inner => lookahead inner
  | .dia _ inner => lookahead inner + 1

theorem trace_diamond (stream : Nat → Bool) (track : Track) (position : Nat)
    (label : PUnit) (formula : Formula Bool PUnit) :
    (system stream).sat (.dia label formula) (.trace track position) ↔
      (system stream).sat formula (.trace track (position + 1)) := by
  change (∃ target, target ∈ [.trace track (position + 1)] ∧ (system stream).sat formula target) ↔ _
  constructor
  · rintro ⟨target, step, holds⟩
    exact List.mem_singleton.mp step ▸ holds
  · intro holds
    exact ⟨_, List.mem_singleton.mpr rfl, holds⟩

/-- Every formula reads only its finite lookahead window on a stream. -/
theorem trace_sat_of_prefix (stream : Nat → Bool) (formula : Formula Bool PUnit)
    (first second : Track) (position : Nat)
    (same : ∀ offset < lookahead formula,
      bit stream first (position + offset) = bit stream second (position + offset)) :
    (system stream).sat formula (.trace first position) ↔
      (system stream).sat formula (.trace second position) := by
  induction formula generalizing position with
  | top => exact Iff.rfl
  | atom atom =>
    have current := same 0 (Nat.zero_lt_succ 0)
    simp only [Nat.add_zero] at current
    change (atom = bit stream first position) ↔ (atom = bit stream second position)
    rw [current]
  | conj left right firstInduction secondInduction =>
    exact and_congr
      (firstInduction position fun offset bound =>
        same offset (Nat.lt_of_lt_of_le bound (Nat.le_max_left _ _)))
      (secondInduction position fun offset bound =>
        same offset (Nat.lt_of_lt_of_le bound (Nat.le_max_right _ _)))
  | neg inner inductionHypothesis =>
    exact not_congr (inductionHypothesis position same)
  | dia label inner inductionHypothesis =>
    refine (trace_diamond stream first position label inner).trans
      ((inductionHypothesis (position + 1) ?_).trans
        (trace_diamond stream second position label inner).symm)
    intro offset bound
    have later := same (offset + 1) (Nat.add_lt_add_right bound 1)
    have reassoc : position + (offset + 1) = position + 1 + offset := by omega
    exact reassoc ▸ later

/-- A finite scan either verifies the even prefix or finds an actual true
even entry. This statement needs no infinite search principle. -/
theorem finite_even_scan (stream : Nat → Bool) (bound : Nat) :
    (∀ offset < bound, stream (2 * offset) = false) ∨
      ∃ offset < bound, stream (2 * offset) = true := by
  induction bound with
  | zero => exact Or.inl (fun _ impossible => (Nat.not_lt_zero _ impossible).elim)
  | succ bound inductionHypothesis =>
    rcases inductionHypothesis with clear | ⟨offset, less, found⟩
    · cases result : stream (2 * bound) with
      | false =>
        apply Or.inl
        intro offset less
        rcases Nat.lt_succ_iff_lt_or_eq.mp less with less | rfl
        · exact clear offset less
        · exact result
      | true => exact Or.inr ⟨bound, Nat.lt_succ_self _, result⟩
    · exact Or.inr ⟨offset, Nat.lt_succ_of_lt less, found⟩

/-- The uniqueness hypothesis is used only to exclude an odd true entry
when the finite scan has found an even one. -/
theorem finite_zero_cover (stream : Nat → Bool)
    (unique : ∀ first second, stream first = true → stream second = true → first = second)
    (bound : Nat) :
    (∀ offset < bound, stream (2 * offset) = false) ∨
      (∀ offset < bound, stream (2 * offset + 1) = false) := by
  rcases finite_even_scan stream bound with clear | ⟨first, _, found⟩
  · exact Or.inl clear
  · apply Or.inr
    intro second _
    cases other : stream (2 * second + 1) with
    | false => rfl
    | true =>
      have impossible := unique _ _ found other
      omega

/-- Two genuinely different roots agree on every finite formula. The branch
used to match the zero stream may depend on the formula's lookahead. -/
theorem roots_logicallyEquivalent (stream : Nat → Bool)
    (unique : ∀ first second, stream first = true → stream second = true → first = second) :
    (system stream).LogicallyEquivalent (.root true) (.root false) := by
  intro formula
  induction formula with
  | top => exact Iff.rfl
  | atom atom => exact Iff.rfl
  | conj first second firstInduction secondInduction => exact and_congr firstInduction secondInduction
  | neg inner inductionHypothesis => exact not_congr inductionHypothesis
  | dia label inner _ =>
    constructor
    · rintro ⟨target, step, holds⟩
      change target ∈ [.trace .even 0, .trace .odd 0, .trace .zero 0] at step
      simp only [List.mem_cons, List.not_mem_nil, or_false] at step
      rcases step with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), holds⟩
      · exact ⟨_, List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)), holds⟩
      · rcases finite_zero_cover stream unique (lookahead inner) with even | odd
        · have comparison := trace_sat_of_prefix stream inner Track.zero Track.even 0
            (fun offset less => by simpa only [bit, Nat.zero_add] using (even offset less).symm)
          exact ⟨_, List.mem_cons.mpr (Or.inl rfl), comparison.mp holds⟩
        · have comparison := trace_sat_of_prefix stream inner Track.zero Track.odd 0
            (fun offset less => by simpa only [bit, Nat.zero_add] using (odd offset less).symm)
          exact ⟨_, List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)), comparison.mp holds⟩
    · rintro ⟨target, step, holds⟩
      change target ∈ [.trace .even 0, .trace .odd 0] at step
      change ∃ target, target ∈ [State.trace .even 0, State.trace .odd 0, State.trace .zero 0] ∧
        (system stream).sat inner target
      simp only [List.mem_cons, List.not_mem_nil, or_false] at step
      rcases step with rfl | rfl
      · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), holds⟩
      · exact ⟨_, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))), holds⟩

/-- A bisimulation matches one stream at all depths with the same branch. -/
theorem stream_zero_of_related (stream : Nat → Bool) {relation : State → State → Prop}
    (bisimulation : (system stream).IsBisimulation relation) (track : Track)
    {position : Nat} (related : relation (.trace .zero position) (.trace track position)) :
    ∀ offset, bit stream track (position + offset) = false := by
  intro offset
  induction offset generalizing position with
  | zero =>
    have current := (bisimulation.2.2 related false).mp rfl
    change false = bit stream track position at current
    simpa only [Nat.add_zero] using current.symm
  | succ offset inductionHypothesis =>
    have step : (system stream).act PUnit.unit (.trace .zero position)
        (.trace .zero (position + 1)) := List.mem_singleton.mpr rfl
    obtain ⟨target, next, continued⟩ := bisimulation.1 related PUnit.unit step
    change target ∈ [.trace track (position + 1)] at next
    have equal := List.mem_singleton.mp next
    subst target
    have later := inductionHypothesis continued
    have reassoc : position + (offset + 1) = position + 1 + offset := by omega
    exact reassoc ▸ later

/-- Matching the added zero branch proves the LLPO disjunction. -/
theorem llpo_of_bisimilar_roots (stream : Nat → Bool)
    (related : (system stream).Bisimilar (.root true) (.root false)) :
    (∀ position, stream (2 * position) = false) ∨
      (∀ position, stream (2 * position + 1) = false) := by
  obtain ⟨relation, bisimulation, roots⟩ := related
  have extra : (system stream).act PUnit.unit (.root true) (.trace .zero 0) :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))))
  obtain ⟨target, step, traces⟩ := bisimulation.1 roots PUnit.unit extra
  change target ∈ [.trace .even 0, .trace .odd 0] at step
  simp only [List.mem_cons, List.not_mem_nil, or_false] at step
  rcases step with rfl | rfl
  · exact Or.inl (fun position => by
      simpa only [bit, Nat.zero_add] using stream_zero_of_related stream bisimulation Track.even traces position)
  · exact Or.inr (fun position => by
      simpa only [bit, Nat.zero_add] using stream_zero_of_related stream bisimulation Track.odd traces position)

/-- A concrete matching relation, with the selected stream retained at every
depth rather than selected afresh for individual observations. -/
inductive Merge (selected : Track) : State → State → Prop where
  | same (state : State) : Merge selected state state
  | roots : Merge selected (.root true) (.root false)
  | stream (position : Nat) : Merge selected (.trace .zero position) (.trace selected position)

theorem merge_bisimulation (stream : Nat → Bool) (selected : Track)
    (original : selected = .even ∨ selected = .odd)
    (clear : ∀ position, bit stream selected position = false) :
    (system stream).IsBisimulation (Merge selected) := by
  have originalStep : reduction (.root false) (.trace selected 0) := by
    rcases original with rfl | rfl
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))
  refine ⟨?_, ?_, ?_⟩
  · intro left right related label target reduces
    cases related with
    | same state => exact ⟨target, reduces, .same target⟩
    | roots =>
      change target ∈ [State.trace .even 0, State.trace .odd 0, State.trace .zero 0] at reduces
      simp only [List.mem_cons, List.not_mem_nil, or_false] at reduces
      rcases reduces with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), .same _⟩
      · exact ⟨_, List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)), .same _⟩
      · exact ⟨_, originalStep, .stream 0⟩
    | stream position =>
      change target ∈ [State.trace .zero (position + 1)] at reduces
      have equal := List.mem_singleton.mp reduces
      subst target
      exact ⟨_, List.mem_singleton.mpr rfl, .stream (position + 1)⟩
  · intro left right related label target reduces
    cases related with
    | same state => exact ⟨target, reduces, .same target⟩
    | roots =>
      change target ∈ [State.trace .even 0, State.trace .odd 0] at reduces
      simp only [List.mem_cons, List.not_mem_nil, or_false] at reduces
      rcases reduces with rfl | rfl
      · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), .same _⟩
      · exact ⟨_, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))), .same _⟩
    | stream position =>
      change target ∈ [State.trace selected (position + 1)] at reduces
      have equal := List.mem_singleton.mp reduces
      subst target
      exact ⟨_, List.mem_singleton.mpr rfl, .stream (position + 1)⟩
  · intro left right related atom
    cases related with
    | same state => exact Iff.rfl
    | roots => exact Iff.rfl
    | stream position =>
      change (atom = false) ↔ (atom = bit stream selected position)
      rw [clear]

/-- The probe's bisimulation equivalence is exactly the infinite branch
decision. Its finite logical agreement above requires only uniqueness of a
true entry, not that decision. -/
theorem roots_bisimilar_iff (stream : Nat → Bool) :
    (system stream).Bisimilar (.root true) (.root false) ↔
      (∀ position, stream (2 * position) = false) ∨
        (∀ position, stream (2 * position + 1) = false) := by
  constructor
  · exact llpo_of_bisimilar_roots stream
  · rintro (clear | clear)
    · exact ⟨Merge .even,
        merge_bisimulation stream .even (Or.inl rfl) clear, .roots⟩
    · exact ⟨Merge .odd,
        merge_bisimulation stream .odd (Or.inr rfl) clear, .roots⟩

namespace Controls

/-- An actual infinite zero stream gives equivalent roots with different
authored equation classes. -/
theorem zero_roots_bisimilar :
    (system (fun _ => false)).Bisimilar (.root true) (.root false) :=
  (roots_bisimilar_iff _).mpr (Or.inl (fun _ => rfl))

theorem roots_not_equated : ¬ theory.Equiv (.root true) (.root false) := by
  intro equal
  have impossible := State.root.inj equal
  exact Bool.noConfusion impossible

/-- When both original streams start true, the extra zero stream is
distinguished by a depth-one formula. This confirms that uniqueness of a true
entry is a real restriction on the logical-agreement theorem. -/
theorem two_initial_pulses_distinguished :
    let stream : Nat → Bool := fun position => decide (position = 0 ∨ position = 1)
    (system stream).sat (.dia PUnit.unit (.atom false)) (.root true) ∧
      ¬ (system stream).sat (.dia PUnit.unit (.atom false)) (.root false) := by
  dsimp
  constructor
  · exact ⟨.trace .zero 0,
      List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))), rfl⟩
  · rintro ⟨target, step, holds⟩
    change target ∈ [State.trace .even 0, State.trace .odd 0] at step
    simp only [List.mem_cons, List.not_mem_nil, or_false] at step
    rcases step with rfl | rfl <;> exact Bool.noConfusion holds

end Controls

/-- Unrestricted finite-branching reflection entails LLPO on arbitrary binary
sequences. The theorem exposes the consequence without adopting either rule. -/
theorem image_finite_reflection_implies_llpo
    (reflection : ∀ (S : GSLT.{0}) (M : System.{0, 0} S), M.ImageFiniteModulo →
      ∀ left right, M.LogicallyEquivalent left right → M.Bisimilar left right)
    (stream : Nat → Bool)
    (unique : ∀ first second, stream first = true → stream second = true → first = second) :
    (∀ position, stream (2 * position) = false) ∨
      (∀ position, stream (2 * position + 1) = false) :=
  llpo_of_bisimilar_roots stream
    (reflection theory (system stream) (imageFinite stream) _ _
      (roots_logicallyEquivalent stream unique))

end Mettapedia.GSLT.ConstructiveModalStrength
