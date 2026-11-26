import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic

/-!
# Safety of replacement checkers

For a safety requirement, the greatest invariant under uncontrolled moves
consists of the states from which those moves cannot reach a violation.
Controlled moves may enter this invariant. Any controller that promises
safety for every continuation can enter only this invariant. On pairs of
an active configuration and a reference configuration, the same construction
gives a lifetime guard for a distance bound.

For exact preservation, observations along ordinary action words determine
dynamic equivalence. A replacement checker must enter the greatest region
in which the already installed checkers preserve that equivalence. The
resulting admission is the largest one certified by a common observable
equivalence preserved by ordinary actions and attempted replacements.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.SafetyInvariant

open Relation

variable {State : Type*}

/-- The greatest invariant included in `good` under the relation `move`. -/
def kernel (move : State → State → Prop) (good : Set State) : Set State :=
  {s | ∀ t, ReflTransGen move s t → t ∈ good}

theorem kernel_good {move : State → State → Prop} {good : Set State} {s : State}
    (safe : s ∈ kernel move good) : s ∈ good :=
  safe s .refl

theorem kernel_closed {move : State → State → Prop} {good : Set State} {s t : State}
    (safe : s ∈ kernel move good) (moves : move s t) : t ∈ kernel move good :=
  fun _ trail => safe _ (trail.head moves)

theorem subset_kernel {move : State → State → Prop} {good invariant : Set State}
    (within : invariant ⊆ good)
    (closed : ∀ ⦃s t⦄, s ∈ invariant → move s t → t ∈ invariant) :
    invariant ⊆ kernel move good := by
  intro s initial t trail
  apply within
  induction trail with
  | refl => exact initial
  | tail _ moved ih => exact closed ih moved

theorem outside_kernel_iff {move : State → State → Prop} {good : Set State} {s : State} :
    s ∉ kernel move good ↔ ∃ t, ReflTransGen move s t ∧ t ∉ good := by
  classical
  simp [kernel]

/-- A run can interleave uncontrolled moves with proposals into the kernel. -/
theorem kernel_after {move propose : State → State → Prop} {good : Set State} {s t : State}
    (safe : s ∈ kernel move good)
    (run : ReflTransGen (fun x y => move x y ∨ propose x y ∧ y ∈ kernel move good) s t) :
    t ∈ kernel move good := by
  induction run with
  | refl => exact safe
  | tail _ step ih =>
      rcases step with moved | ⟨_, admitted⟩
      · exact kernel_closed ih moved
      · exact admitted

/-- A safe controller cannot admit a move from a reached state into a state
with an uncontrolled path to a violation. History can be carried in the state. -/
theorem controlled_target_in_kernel {move allow : State → State → Prop}
    {good : Set State} {initial current target : State}
    (safeRun : ∀ s, ReflTransGen (fun x y => move x y ∨ allow x y) initial s → s ∈ good)
    (reached : ReflTransGen (fun x y => move x y ∨ allow x y) initial current)
    (admitted : allow current target) :
    target ∈ kernel move good := by
  intro s continuation
  have carried : ReflTransGen (fun x y => move x y ∨ allow x y) target s :=
    ReflTransGen.mono (fun _ _ h => Or.inl h) target s continuation
  exact safeRun s ((reached.tail (Or.inr admitted)).trans carried)

/-- An abstraction which matches uncontrolled steps in both directions pulls
back the kernel of the observed safety requirement. -/
theorem kernel_readback {View : Type*} (read : State → View)
    (move : State → State → Prop) (moveView : View → View → Prop) (good : Set View)
    (sound : ∀ ⦃s t⦄, move s t → moveView (read s) (read t))
    (complete : ∀ s v, moveView (read s) v → ∃ t, move s t ∧ read t = v)
    (s : State) :
    s ∈ kernel move (read ⁻¹' good) ↔ read s ∈ kernel moveView good := by
  have lift {v : View} (trail : ReflTransGen moveView (read s) v) :
      ∃ t, ReflTransGen move s t ∧ read t = v := by
    induction trail with
    | refl => exact ⟨s, .refl, rfl⟩
    | tail _ step ih =>
        obtain ⟨previous, reached, rfl⟩ := ih
        obtain ⟨target, moved, rfl⟩ := complete previous _ step
        exact ⟨target, reached.tail moved, rfl⟩
  refine ⟨?_, fun safe t trail => safe (read t) (trail.lift read sound)⟩
  intro safe v trail
  obtain ⟨t, reached, rfl⟩ := lift trail
  exact safe t reached

end Mettapedia.GSLT.Distinction.SafetyInvariant

namespace Mettapedia.GSLT.Distinction.ReflectiveSafety

open SafetyInvariant

variable {State Action Proposal Observation : Type*}

/-- A policy is being synthesized at the designated states. At all other
states the installed checker's verdicts are part of the given dynamics. -/
structure System (State Action Proposal Observation : Type*) where
  read : State → Observation
  run : Action → State → State
  revise : Proposal → State → State
  designated : State → Bool
  installed : Proposal → State → Bool
  run_preserves_designated : ∀ a s, designated s = true → designated (run a s) = true

namespace System

variable (M : System State Action Proposal Observation)

def DynamicEq (first second : State) : Prop :=
  ∀ word : List Action, M.read (word.foldl (fun s a => M.run a s) first) =
    M.read (word.foldl (fun s a => M.run a s) second)

theorem dynamic_equivalence : Equivalence M.DynamicEq where
  refl _ _ := rfl
  symm same word := (same word).symm
  trans first second word := (first word).trans (second word)

theorem dynamic_run {s t : State} (same : M.DynamicEq s t) (a : Action) :
    M.DynamicEq (M.run a s) (M.run a t) :=
  fun word => same (a :: word)

def Uncontrolled (s t : State) : Prop :=
  (∃ a, t = M.run a s) ∨
    (∃ p, M.designated s = false ∧ M.installed p s = true ∧ t = M.revise p s)

def LocallySafe : Set State :=
  {s | ∀ p, M.designated s = false → M.installed p s = true → M.DynamicEq s (M.revise p s)}

def Safe : Set State :=
  kernel M.Uncontrolled M.LocallySafe

theorem designated_safe {s : State} (here : M.designated s = true) : s ∈ M.Safe := by
  apply subset_kernel (invariant := {t | M.designated t = true}) ?_ ?_ here
  · intro t ht _ absent _
    exact (Bool.false_ne_true (absent.symm.trans ht)).elim
  · rintro t _ ht (⟨a, rfl⟩ | ⟨_, absent, _, rfl⟩)
    · exact M.run_preserves_designated a t ht
    · exact (Bool.false_ne_true (absent.symm.trans ht)).elim

abbrev Gate (State Proposal : Type*) := Proposal → State → Prop

open Classical in
noncomputable def attempt (gate : Gate State Proposal) (p : Proposal) (s : State) : State :=
  if M.designated s then
    if gate p s then M.revise p s else s
  else if M.installed p s then M.revise p s else s

/-- The gate which checks both the ordinary behavior and the future
admissions of the checker that would be installed. -/
def exactGate (p : Proposal) (s : State) : Prop :=
  M.DynamicEq s (M.revise p s) ∧ M.revise p s ∈ M.Safe

/-- A proof of exactness supplies a common observable equivalence stable
under every proposed action and relating each admitted change. -/
structure ExactCertificate (gate : Gate State Proposal) where
  related : State → State → Prop
  equivalence : Equivalence related
  observes : ∀ ⦃s t⦄, related s t → M.read s = M.read t
  ordinary : ∀ ⦃s t⦄, related s t → ∀ a, related (M.run a s) (M.run a t)
  attempts : ∀ ⦃s t⦄, related s t → ∀ p, related (M.attempt gate p s) (M.attempt gate p t)
  admitted : ∀ s p, M.designated s = true → gate p s → related s (M.revise p s)

theorem ExactCertificate.dynamic {M : System State Action Proposal Observation}
    {gate : Gate State Proposal} (C : M.ExactCertificate gate)
    {s t : State} (related : C.related s t) : M.DynamicEq s t := by
  intro word
  induction word generalizing s t with
  | nil => exact C.observes related
  | cons a word ih => exact ih (C.ordinary related a)

theorem safe_attempt {s : State} (safe : s ∈ M.Safe) (p : Proposal) :
    M.DynamicEq s (M.attempt M.exactGate p s) ∧ M.attempt M.exactGate p s ∈ M.Safe := by
  classical
  cases here : M.designated s with
  | false =>
      cases admitted : M.installed p s with
      | false => simpa [attempt, here, admitted] using ⟨M.dynamic_equivalence.refl s, safe⟩
      | true =>
          have valid := kernel_good safe
          have moved : M.Uncontrolled s (M.revise p s) := Or.inr ⟨p, here, admitted, rfl⟩
          simpa [attempt, here, admitted] using ⟨valid p here admitted, kernel_closed safe moved⟩
  | true =>
      by_cases admitted : M.exactGate p s
      · rw [attempt, if_pos here, if_pos admitted]
        exact admitted
      · simpa [attempt, here, admitted] using ⟨M.dynamic_equivalence.refl s, safe⟩

def SafeEquivalence (s t : State) : Prop :=
  s = t ∨ s ∈ M.Safe ∧ t ∈ M.Safe ∧ M.DynamicEq s t

/-- On the safe region the certificate uses exactly ordinary equivalence.
All other states can be left in singleton classes. -/
noncomputable def exactCertificate : M.ExactCertificate M.exactGate where
  related := M.SafeEquivalence
  equivalence :=
    ⟨fun _ => Or.inl rfl,
      fun h => h.elim (fun eq => Or.inl eq.symm)
        (fun ⟨s, t, e⟩ => Or.inr ⟨t, s, M.dynamic_equivalence.symm e⟩),
      fun h h' => by
        rcases h with rfl | ⟨s, _, eq⟩
        · exact h'
        rcases h' with rfl | ⟨_, t, eq'⟩
        · exact Or.inr ⟨s, by assumption, eq⟩
        · exact Or.inr ⟨s, t, M.dynamic_equivalence.trans eq eq'⟩⟩
  observes := by
    rintro _ _ (rfl | ⟨_, _, equal⟩)
    · rfl
    · exact equal []
  ordinary := by
    rintro s t (rfl | ⟨atS, atT, equal⟩) a
    · exact Or.inl rfl
    · exact Or.inr ⟨kernel_closed atS (Or.inl ⟨a, rfl⟩),
        kernel_closed atT (Or.inl ⟨a, rfl⟩), M.dynamic_run equal a⟩
  attempts := by
    rintro s t (rfl | ⟨atS, atT, equal⟩) p
    · exact Or.inl rfl
    · obtain ⟨first, safeFirst⟩ := M.safe_attempt atS p
      obtain ⟨last, safeLast⟩ := M.safe_attempt atT p
      exact Or.inr ⟨safeFirst, safeLast, M.dynamic_equivalence.trans
        (M.dynamic_equivalence.symm first) (M.dynamic_equivalence.trans equal last)⟩
  admitted := fun _ _ here ⟨same, safe⟩ => Or.inr ⟨M.designated_safe here, safe, same⟩

private theorem ExactCertificate.attempt_equiv {M : System State Action Proposal Observation}
    {gate : Gate State Proposal}
    (C : M.ExactCertificate gate) {s : State} (here : M.designated s = true) (p : Proposal) :
    C.related s (M.attempt gate p s) := by
  classical
  by_cases admitted : gate p s
  · simpa [attempt, here, admitted] using C.admitted s p here admitted
  · simpa [attempt, here, admitted] using C.equivalence.refl s

private theorem ExactCertificate.peer_safe {M : System State Action Proposal Observation}
    {gate : Gate State Proposal} (C : M.ExactCertificate gate)
    {s t : State} (here : M.designated t = true) (related : C.related s t) : s ∈ M.Safe := by
  let peers : Set State := {x | ∃ y, M.designated y = true ∧ C.related x y}
  have installed_stays {x y : State} (marked : M.designated y = true) (same : C.related x y)
      (p : Proposal) (elsewhere : M.designated x = false) (admitted : M.installed p x = true) :
      C.related (M.revise p x) y := by
    have moved := C.attempts same p
    have rel := C.equivalence.trans moved (C.equivalence.symm (C.attempt_equiv marked p))
    simpa [attempt, elsewhere, admitted] using rel
  apply subset_kernel (invariant := peers) ?_ ?_ ⟨t, here, related⟩
  · rintro x ⟨y, marked, same⟩ p elsewhere admitted
    exact C.dynamic (C.equivalence.trans same (C.equivalence.symm (installed_stays marked same p elsewhere admitted)))
  · rintro x _ ⟨y, marked, same⟩ (⟨a, rfl⟩ | ⟨p, elsewhere, admitted, rfl⟩)
    · exact ⟨M.run a y, M.run_preserves_designated a y marked, C.ordinary same a⟩
    · exact ⟨y, marked, installed_stays marked same p elsewhere admitted⟩

/-- Every exactly certified policy is contained in the synthesized gate. -/
theorem exactGate_largest {gate : Gate State Proposal} (C : M.ExactCertificate gate)
    {s : State} (here : M.designated s = true) (p : Proposal) (allowed : gate p s) :
    M.exactGate p s := by
  have related := C.admitted s p here allowed
  exact ⟨C.dynamic related, C.peer_safe here (C.equivalence.symm related)⟩

noncomputable def runEvent (gate : Gate State Proposal) (event : Action ⊕ Proposal) (s : State) : State :=
  match event with
  | .inl a => M.run a s
  | .inr p => M.attempt gate p s

/-- Agreement on every finite word, including proposed replacements. -/
def ReflectiveEq (gate : Gate State Proposal) (s t : State) : Prop :=
  ∀ word : List (Action ⊕ Proposal), M.read (word.foldl (fun x e => M.runEvent gate e x) s) =
    M.read (word.foldl (fun x e => M.runEvent gate e x) t)

theorem ExactCertificate.reflective {M : System State Action Proposal Observation}
    {gate : Gate State Proposal} (C : M.ExactCertificate gate)
    {s t : State} (related : C.related s t) : M.ReflectiveEq gate s t := by
  intro word
  induction word generalizing s t with
  | nil => exact C.observes related
  | cons first word ih =>
      cases first with
      | inl a => exact ih (C.ordinary related a)
      | inr p => exact ih (C.attempts related p)

/-- A policy preserving all future observations on its admitted edits
has the canonical certificate given by equality of those observations. -/
def certificate_of_reflective {gate : Gate State Proposal}
    (sound : ∀ s p, M.designated s = true → gate p s → M.ReflectiveEq gate s (M.revise p s)) :
    M.ExactCertificate gate where
  related := M.ReflectiveEq gate
  equivalence :=
    ⟨fun _ _ => rfl, fun h word => (h word).symm, fun h h' word => (h word).trans (h' word)⟩
  observes := by
    intro _ _ h
    exact h []
  ordinary := by
    intro _ _ h a word
    exact h (.inl a :: word)
  attempts := by
    intro _ _ h p word
    exact h (.inr p :: word)
  admitted := sound

theorem exactGate_iff_reflective {s : State} (here : M.designated s = true) (p : Proposal) :
    M.exactGate p s ↔ M.ReflectiveEq M.exactGate s (M.revise p s) := by
  have sound (x : State) (proposal : Proposal) (marked : M.designated x = true)
      (admitted : M.exactGate proposal x) : M.ReflectiveEq M.exactGate x (M.revise proposal x) :=
    M.exactCertificate.reflective (M.exactCertificate.admitted x proposal marked admitted)
  let C := M.certificate_of_reflective sound
  exact ⟨sound s p here, fun same => ⟨C.dynamic same, C.peer_safe here (C.equivalence.symm same)⟩⟩

/-- Revisions are invisible along every finite run of the synthesized
policy. Delete the attempted revisions to run the unmodified twin. -/
theorem follows_twin (word : List (Action ⊕ Proposal)) {s t : State}
    (safe : s ∈ M.Safe) (same : M.DynamicEq s t) :
    M.DynamicEq (word.foldl (fun x event => M.runEvent M.exactGate event x) s)
      ((word.filterMap fun event => event.elim some (fun _ => none)).foldl (fun x a => M.run a x) t) := by
  induction word generalizing s t with
  | nil => exact same
  | cons first word ih =>
      cases first with
      | inl a => exact ih (kernel_closed safe (Or.inl ⟨a, rfl⟩)) (M.dynamic_run same a)
      | inr p =>
          obtain ⟨unchanged, remainsSafe⟩ := M.safe_attempt safe p
          exact ih remainsSafe (M.dynamic_equivalence.trans (M.dynamic_equivalence.symm unchanged) same)

/-! ## Lifetime contracts -/

/-- An ordinary event moves both configurations. A legacy admission moves
only the active one. -/
def TwinMove (x y : State × State) : Prop :=
  (∃ a, y = (M.run a x.1, M.run a x.2)) ∨
    (∃ p, M.designated x.1 = false ∧ M.installed p x.1 = true ∧ y = (M.revise p x.1, x.2))

def TwinProposal (x y : State × State) : Prop :=
  M.designated x.1 = true ∧ ∃ p, y = (M.revise p x.1, x.2)

/-- For a lifetime bound, `good` is the set of pairs within the budget. -/
def lifetimeDomain (good : Set (State × State)) : Set (State × State) :=
  kernel M.TwinMove good

theorem diagonal_in_lifetimeDomain {good : Set (State × State)}
    (diagonal : ∀ x, (x, x) ∈ good) (s : State) (here : M.designated s = true) :
    (s, s) ∈ M.lifetimeDomain good := by
  let paired : Set (State × State) := {x | x.1 = x.2 ∧ M.designated x.1 = true}
  apply subset_kernel (invariant := paired) ?_ ?_ ⟨rfl, here⟩
  · rintro ⟨x, y⟩ ⟨equal, _⟩
    change x = y at equal
    subst y
    exact diagonal x
  · rintro ⟨x, y⟩ _ ⟨equal, marked⟩ (⟨a, rfl⟩ | ⟨p, legacy, _, rfl⟩)
    · exact ⟨congrArg (M.run a) equal, M.run_preserves_designated a x marked⟩
    · exact (Bool.false_ne_true (legacy.symm.trans marked)).elim

theorem lifetime_guard_sound (good : Set (State × State)) {s t : State × State}
    (safe : s ∈ M.lifetimeDomain good)
    (run : Relation.ReflTransGen
      (fun x y => M.TwinMove x y ∨ M.TwinProposal x y ∧ y ∈ M.lifetimeDomain good) s t) :
    t ∈ good :=
  kernel_good (kernel_after safe run)

theorem lifetime_guard_largest {good : Set (State × State)} {policy : State × State → State × State → Prop}
    {s x y : State × State}
    (sound : ∀ t, Relation.ReflTransGen (fun a b => M.TwinMove a b ∨ policy a b) s t → t ∈ good)
    (reached : Relation.ReflTransGen (fun a b => M.TwinMove a b ∨ policy a b) s x)
    (admitted : policy x y) : y ∈ M.lifetimeDomain good :=
  controlled_target_in_kernel sound reached admitted

/-- At zero distance, the lifetime invariant is exactly dynamic
equivalence on the safe region. -/
theorem zero_lifetimeDomain {s t : State} :
    (s, t) ∈ M.lifetimeDomain {x | M.DynamicEq x.1 x.2} ↔ s ∈ M.Safe ∧ M.DynamicEq s t := by
  let good : Set (State × State) := {x | M.DynamicEq x.1 x.2}
  constructor
  · intro safe
    let active : Set State := {x | ∃ y, (x, y) ∈ M.lifetimeDomain good}
    refine ⟨?_, kernel_good safe⟩
    apply subset_kernel (invariant := active) ?_ ?_ ⟨t, safe⟩
    · rintro x ⟨y, holds⟩ p legacy admitted
      have step : M.TwinMove (x, y) (M.revise p x, y) := Or.inr ⟨p, legacy, admitted, rfl⟩
      have before : M.DynamicEq x y := kernel_good holds
      have after : M.DynamicEq (M.revise p x) y := kernel_good (kernel_closed holds step)
      exact M.dynamic_equivalence.trans before (M.dynamic_equivalence.symm after)
    · rintro x _ ⟨y, holds⟩ (⟨a, rfl⟩ | ⟨p, legacy, admitted, rfl⟩)
      · exact ⟨M.run a y, kernel_closed holds (Or.inl ⟨a, rfl⟩)⟩
      · exact ⟨y, kernel_closed holds (Or.inr ⟨p, legacy, admitted, rfl⟩)⟩
  · rintro ⟨safe, eq⟩
    apply subset_kernel (invariant := {x | x.1 ∈ M.Safe ∧ M.DynamicEq x.1 x.2}) ?_ ?_ ⟨safe, eq⟩
    · rintro _ ⟨_, equal⟩
      exact equal
    · rintro ⟨x, y⟩ _ ⟨holds, same⟩ (⟨a, rfl⟩ | ⟨p, legacy, admitted, rfl⟩)
      · exact ⟨kernel_closed holds (Or.inl ⟨a, rfl⟩), M.dynamic_run same a⟩
      · have allowed : M.DynamicEq x (M.revise p x) := kernel_good holds p legacy admitted
        exact ⟨kernel_closed holds (Or.inr ⟨p, legacy, admitted, rfl⟩),
          M.dynamic_equivalence.trans (M.dynamic_equivalence.symm allowed) same⟩

/-- At an exact pair, the zero-budget lifetime rule and the reflective gate
agree on each proposed revision. -/
theorem zero_lifetime_iff_exactGate {s t : State} (same : M.DynamicEq s t) (p : Proposal) :
    (M.revise p s, t) ∈ M.lifetimeDomain {x | M.DynamicEq x.1 x.2} ↔ M.exactGate p s := by
  rw [M.zero_lifetimeDomain]
  constructor
  · rintro ⟨safe, related⟩
    exact ⟨M.dynamic_equivalence.trans same (M.dynamic_equivalence.symm related), safe⟩
  · rintro ⟨related, safe⟩
    exact ⟨safe, M.dynamic_equivalence.trans (M.dynamic_equivalence.symm related) same⟩

end System

namespace Controls

/-- The first replacement can only install a weaker checker one move later.
A second replacement leaves a checker with no legacy admissions installed. -/
def machine : System (Fin 5) Unit (Fin 4) Bool where
  read s := s == 4
  run _ s := s
  revise p s :=
    if s == 0 && p == 0 then 1 else
    if s == 0 && p == 1 then 3 else
    if s == 1 && p == 2 then 2 else
    if s == 2 && p == 3 then 4 else s
  designated s := s == 0
  installed p s := (s == 1 && p == 2) || (s == 2 && p == 3)
  run_preserves_designated _ _ h := h

private theorem same_read {s t : Fin 5} (same : machine.read s = machine.read t) :
    machine.DynamicEq s t := by
  have run_id (word : List Unit) (x : Fin 5) :
      word.foldl (fun y a => machine.run a y) x = x := by
    induction word with
    | nil => rfl
    | cons _ _ ih => exact ih
  intro word
  rwa [run_id, run_id]

theorem dynamic_test_alone_allows_chain :
    machine.DynamicEq 0 (machine.revise 0 0) := same_read (by decide)

theorem exact_guard_refuses_chain : ¬ machine.exactGate 0 0 := by
  intro approval
  have safe : (1 : Fin 5) ∈ machine.Safe := approval.2
  have moved : machine.Uncontrolled 1 2 := .inr ⟨2, by decide, by decide, rfl⟩
  have locally := kernel_good (kernel_closed safe moved)
  have distinct := (locally 3 (by decide) (by decide)) []
  exact Bool.false_ne_true distinct

theorem exact_guard_accepts_frozen_checker : machine.exactGate 1 0 := by
  refine ⟨same_read (by decide), ?_⟩
  change (3 : Fin 5) ∈ machine.Safe
  apply subset_kernel (invariant := {x | x = 3}) ?_ ?_ rfl
  · rintro _ (rfl : _ = (3 : Fin 5)) p _ denied
    have none : machine.installed p 3 = false := by simp [machine]
    rw [none] at denied
    cases denied
  · rintro _ _ (rfl : _ = (3 : Fin 5)) (⟨_, rfl⟩ | ⟨p, _, denied, rfl⟩)
    · rfl
    · have none : machine.installed p 3 = false := by simp [machine]
      rw [none] at denied
      cases denied

end Controls

#print axioms SafetyInvariant.controlled_target_in_kernel
#print axioms SafetyInvariant.kernel_readback
#print axioms System.exactCertificate
#print axioms System.exactGate_largest
#print axioms System.exactGate_iff_reflective
#print axioms System.follows_twin
#print axioms System.lifetime_guard_largest
#print axioms System.zero_lifetime_iff_exactGate
#print axioms Controls.exact_guard_refuses_chain

end Mettapedia.GSLT.Distinction.ReflectiveSafety
