import Mettapedia.Languages.MeTTa.SubstitutionAlgebra

/-!
# Occurs checks at a fresh activation frame

A triangular substitution — a binding's value may mention bound variables —
must stay acyclic: no binding's value may reach its own variable.  Binding a
variable therefore normally carries an occurs check.

An activation frame minted for one equation attempt has variables that no
existing binding mentions.  `FrameFresh` states the invariant: no binding's
value, inside or outside the frame, mentions a frame variable.  Under it a
value that avoids the frame reaches no frame variable (`no_reach_of_avoids`),
so the occurs check at a frame slot has nothing to find, and binding the slot
keeps both acyclicity and the invariant (`bind_frame_preserves`) — across any
sequence of such writes (`bindAll_frame_preserves`), which is how a frame's
slots are published.

The premise is necessary.  A write to an outer variable whose value mentions
the frame lets a frame-avoiding value reach a frame variable, and binding that
variable then closes a cycle (`outer_write_breaks_elision`).  An outer write
whose value avoids the frame keeps the invariant (`bind_preserves_frameFresh`).

CeTTa realizes this in `src/match.c`: `bindings_exclusive_frame_begin_fresh`
marks a frame whose identity was minted for the activation, and the exclusive
store elides the reachability walk exactly under the premises of
`bind_frame_preserves` — a local slot, a value that avoids the frame, and no
earlier stored value that mentions it.  The first value that mentions the
frame, at a local or an outer variable, ends the elision, and publication
passes the same verdict as evidence.  Relating the C store to `Subst`, and the
frame's identity allocator to `FrameFresh`, remains a realization obligation.

A second absence proof comes from a summary of the variables bound values
mention: when the summary covers every bound value and misses `x`, a value
that does not mention `x` cannot reach it (`bind_acyclic_of_covered`).  The
proof needs coverage of every bound value (`uncovered_summary_admits_cycle`).
CeTTa's summary is `rhs_variable_bloom`, consulted by `bindings_bind_evidence`,
so every write of a bound value, to a row or to a frame slot, adds that
value's variables (`bind_preserves_covers`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.FreshFrameOccursCheck

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Var Subst vars)

/-- Resolving `t` through `σ` can expose the variable `y`. -/
inductive Reaches (σ : Subst) : Atom → Var → Prop
  | here {t : Atom} {y : Var} : y ∈ vars t → Reaches σ t y
  | through {t u : Atom} {x y : Var} :
      x ∈ vars t → σ x = some u → Reaches σ u y → Reaches σ t y

/-- No binding's value reaches its own variable. -/
def Acyclic (σ : Subst) : Prop :=
  ∀ x u, σ x = some u → ¬ Reaches σ u x

/-- The term mentions no variable of the frame. -/
def Avoids (frame : Var → Prop) (t : Atom) : Prop :=
  ∀ v ∈ vars t, ¬ frame v

/-- No binding's value mentions a variable of the frame. -/
def FrameFresh (frame : Var → Prop) (σ : Subst) : Prop :=
  ∀ x u, σ x = some u → Avoids frame u

/-- Bind one variable, leaving every other binding as it was. -/
def bind (σ : Subst) (x : Var) (t : Atom) : Subst :=
  fun y => if y = x then some t else σ y

theorem bind_self (σ : Subst) (x : Var) (t : Atom) : bind σ x t x = some t := by
  simp [bind]

theorem bind_other (σ : Subst) {x y : Var} (t : Atom) (distinct : y ≠ x) :
    bind σ x t y = σ y := by
  simp [bind, distinct]

/-! ## Freshness makes the frame unreachable -/

/-- A frame-avoiding value reaches no frame variable while every binding
avoids the frame. -/
theorem no_reach_of_avoids {frame : Var → Prop} {σ : Subst}
    (fresh : FrameFresh frame σ) {t : Atom} (avoids : Avoids frame t)
    {y : Var} (reach : Reaches σ t y) : ¬ frame y := by
  induction reach with
  | here member => exact avoids _ member
  | through _ bound _ ih => exact ih (fresh _ _ bound)

/-- The occurs check at a frame slot is vacuous. -/
theorem occurs_check_vacuous {frame : Var → Prop} {σ : Subst}
    (fresh : FrameFresh frame σ) {t : Atom} (avoids : Avoids frame t)
    {v : Var} (local_slot : frame v) : ¬ Reaches σ t v :=
  fun reach => no_reach_of_avoids fresh avoids reach local_slot

/-- A path starting outside the frame uses only bindings of variables outside
the frame, so it survives any change to frame bindings. -/
theorem reaches_of_agree_off_frame {frame : Var → Prop} {σ τ : Subst}
    (fresh : FrameFresh frame σ)
    (agree : ∀ x, ¬ frame x → σ x = τ x)
    {t : Atom} (avoids : Avoids frame t) {y : Var}
    (reach : Reaches σ t y) : Reaches τ t y := by
  induction reach with
  | here member => exact .here member
  | through member bound _ ih =>
      exact .through member
        ((agree _ (avoids _ member)).symm.trans bound)
        (ih (fresh _ _ bound))

theorem bind_preserves_frameFresh {frame : Var → Prop} {σ : Subst}
    (fresh : FrameFresh frame σ) (x : Var) {t : Atom}
    (avoids : Avoids frame t) : FrameFresh frame (bind σ x t) := by
  intro y u bound
  by_cases same : y = x
  · subst same
    rw [bind_self] at bound
    cases bound
    exact avoids
  · rw [bind_other σ t same] at bound
    exact fresh y u bound

/-- Binding a frame slot to a frame-avoiding value keeps the substitution
acyclic and the frame fresh, with no occurs check performed. -/
theorem bind_frame_preserves {frame : Var → Prop} {σ : Subst}
    (acyclic : Acyclic σ) (fresh : FrameFresh frame σ)
    {v : Var} (local_slot : frame v) {t : Atom} (avoids : Avoids frame t) :
    Acyclic (bind σ v t) ∧ FrameFresh frame (bind σ v t) := by
  have fresh' := bind_preserves_frameFresh fresh v avoids
  refine ⟨?_, fresh'⟩
  intro y u bound reach
  by_cases same : y = v
  · subst same
    rw [bind_self] at bound
    cases bound
    exact occurs_check_vacuous fresh' avoids local_slot reach
  · rw [bind_other σ t same] at bound
    have back : Reaches σ u y :=
      reaches_of_agree_off_frame fresh'
        (fun x off => by
          have distinct : x ≠ v := fun h => off (h ▸ local_slot)
          rw [bind_other σ t distinct])
        (fresh y u bound) reach
    exact acyclic y u bound back

/-- A frame's slot writes, in the order they are published. -/
def bindAll (σ : Subst) : List (Var × Atom) → Subst
  | [] => σ
  | (v, t) :: rest => bindAll (bind σ v t) rest

theorem bindAll_frame_preserves {frame : Var → Prop} :
    ∀ (writes : List (Var × Atom)) {σ : Subst},
      Acyclic σ → FrameFresh frame σ →
      (∀ w ∈ writes, frame w.1 ∧ Avoids frame w.2) →
      Acyclic (bindAll σ writes) ∧ FrameFresh frame (bindAll σ writes)
  | [], _, acyclic, fresh, _ => ⟨acyclic, fresh⟩
  | (v, t) :: rest, _, acyclic, fresh, local_writes => by
      have head := local_writes (v, t) (List.mem_cons_self ..)
      have step := bind_frame_preserves acyclic fresh head.1 head.2
      exact bindAll_frame_preserves rest step.1 step.2
        (fun w member => local_writes w (List.mem_cons_of_mem _ member))

/-! ## The premise is necessary -/

private def fixtureFrame : Var → Prop := fun y => y = "x"

private def cycleValue : Atom :=
  .expression [.symbol "h", .var "x"]

/-- After the outer write `q := (h x)`, a value mentioning only `q` reaches
the frame variable `x`, and binding `x := q` closes the cycle
`x → q → (h x)`. -/
theorem outer_write_breaks_elision :
    let σ := bind (fun _ => none) "q" cycleValue
    Avoids fixtureFrame (.var "q") ∧ fixtureFrame "x" ∧
      Reaches σ (.var "q") "x" ∧ ¬ FrameFresh fixtureFrame σ ∧
      ¬ Acyclic (bind σ "x" (.var "q")) := by
  have xMember : ("x" : Var) ∈ vars cycleValue := by decide
  have qMember : ("q" : Var) ∈ vars (.var "q") := by decide
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · intro v member
    simp [vars] at member
    simp [fixtureFrame, member]
  · exact .through qMember (bind_self _ _ _) (.here xMember)
  · intro fresh
    exact fresh "q" cycleValue (bind_self _ _ _) "x" xMember rfl
  · intro acyclic
    refine acyclic "x" (.var "q") (bind_self _ _ _) ?_
    exact .through qMember (bind_other _ _ (by decide))
      (.here xMember)

/-- A frame-avoiding outer write keeps the invariant, so elision stays sound
after it. -/
theorem outer_avoiding_write_keeps_fresh :
    FrameFresh fixtureFrame (bind (fun _ => none) "q" (.symbol "leaf")) :=
  bind_preserves_frameFresh (fun _ _ none_bound => by cases none_bound) "q"
    (fun _ member => by simp [vars] at member)

/-! ## A summary of the variables of bound values

A store can keep a conservative summary of the variables its bound values
mention.  A path from a value to `x` ends at an occurrence of `x`, either in
the value itself or in some bound value.  So when the summary covers every
bound value and misses `x`, a value that does not mention `x` cannot reach it
(`not_reaches_of_covered`), and binding `x` to it keeps the substitution
acyclic (`bind_acyclic_of_covered`).  A write that adds its value's variables
to the summary keeps it covering (`bind_preserves_covers`).  Coverage is
necessary: a summary that misses one bound value certifies the absence of a
path that exists (`uncovered_summary_admits_cycle`). -/

/-- The summary holds every variable of every bound value. -/
def Covers (summary : Var → Prop) (σ : Subst) : Prop :=
  ∀ x u, σ x = some u → ∀ v ∈ vars u, summary v

/-- Composing a path to a bound variable with a path out of its value. -/
theorem reaches_trans {σ : Subst} {s : Atom} {y z : Var} {u : Atom}
    (first : Reaches σ s y) (bound : σ y = some u) (rest : Reaches σ u z) :
    Reaches σ s z := by
  induction first with
  | here member => exact .through member bound rest
  | through member bound' _ ih => exact .through member bound' (ih bound)

/-- A path under `bind σ x t` either is a path under `σ`, or reaches `x`
under `σ` and continues from `t`. -/
theorem reaches_bind_cases {σ : Subst} {x : Var} {t s : Atom} {z : Var}
    (reach : Reaches (bind σ x t) s z) :
    Reaches σ s z ∨ (Reaches σ s x ∧ Reaches (bind σ x t) t z) := by
  induction reach with
  | here member => exact .inl (.here member)
  | @through s u y z member bound rest ih =>
      by_cases same : y = x
      · subst same
        rw [bind_self] at bound
        cases bound
        exact .inr ⟨.here member, rest⟩
      · rw [bind_other σ t same] at bound
        rcases ih with direct | ⟨to_x, from_t⟩
        · exact .inl (.through member bound direct)
        · exact .inr ⟨.through member bound to_x, from_t⟩

/-- Binding `x` to a value that cannot reach it keeps an acyclic
substitution acyclic. -/
theorem bind_acyclic_of_not_reaches {σ : Subst} (acyclic : Acyclic σ)
    {x : Var} {t : Atom} (no_path : ¬ Reaches σ t x) :
    Acyclic (bind σ x t) := by
  intro y u bound reach
  by_cases same : y = x
  · subst same
    rw [bind_self] at bound
    cases bound
    rcases reaches_bind_cases reach with direct | ⟨to_x, _⟩
    · exact no_path direct
    · exact no_path to_x
  · rw [bind_other σ t same] at bound
    rcases reaches_bind_cases reach with direct | ⟨to_x, from_t⟩
    · exact acyclic y u bound direct
    · rcases reaches_bind_cases from_t with to_y | ⟨t_to_x, _⟩
      · exact no_path (reaches_trans to_y bound to_x)
      · exact no_path t_to_x

theorem not_reaches_of_covered {summary : Var → Prop} {σ : Subst}
    (cover : Covers summary σ) {x : Var} (unsummarized : ¬ summary x)
    {t : Atom} (absent : x ∉ vars t) : ¬ Reaches σ t x := by
  intro reach
  induction reach with
  | here member => exact absent member
  | through _ bound _ ih =>
      exact ih unsummarized
        (fun member => unsummarized (cover _ _ bound _ member))

/-- The absence proof a bind may take from a covering summary. -/
theorem bind_acyclic_of_covered {summary : Var → Prop} {σ : Subst}
    (acyclic : Acyclic σ) (cover : Covers summary σ) {x : Var}
    (unsummarized : ¬ summary x) {t : Atom} (absent : x ∉ vars t) :
    Acyclic (bind σ x t) :=
  bind_acyclic_of_not_reaches acyclic
    (not_reaches_of_covered cover unsummarized absent)

/-- A write whose value's variables join the summary keeps it covering. -/
theorem bind_preserves_covers {summary : Var → Prop} {σ : Subst}
    (cover : Covers summary σ) (x : Var) {t : Atom}
    (added : ∀ v ∈ vars t, summary v) : Covers summary (bind σ x t) := by
  intro y u bound
  by_cases same : y = x
  · subst same
    rw [bind_self] at bound
    cases bound
    exact added
  · rw [bind_other σ t same] at bound
    exact cover y u bound

private def publishedSlot : Atom := .expression [.symbol "h", .var "c"]

/-- A slot `a := (h c)` written without adding `c` to the summary: the
summary misses `c` and the value `(w a)` does not mention it, yet `(w a)`
reaches `c`, and binding `c := (w a)` closes the cycle `c → a → c`. -/
theorem uncovered_summary_admits_cycle :
    let σ := bind (fun _ => none) "a" publishedSlot
    let value : Atom := .expression [.symbol "w", .var "a"]
    ¬ Covers (fun _ => False) σ ∧ ("c" : Var) ∉ vars value ∧
      Reaches σ value "c" ∧ ¬ Acyclic (bind σ "c" value) := by
  have cMember : ("c" : Var) ∈ vars publishedSlot := by decide
  have aMember : ("a" : Var) ∈
      vars (.expression [.symbol "w", .var "a"]) := by decide
  have path : Reaches (bind (fun _ => none) "a" publishedSlot)
      (.expression [.symbol "w", .var "a"]) "c" :=
    .through aMember (bind_self _ _ _) (.here cMember)
  refine ⟨?_, by decide, path, ?_⟩
  · intro cover
    exact cover "a" publishedSlot (bind_self _ _ _) "c" cMember
  · intro acyclic
    refine acyclic "c" _ (bind_self _ _ _) ?_
    exact .through aMember (bind_other _ _ (by decide)) (.here cMember)

/-- Positive control: from the empty substitution, a frame slot bound to a
value over outer variables leaves an acyclic substitution without any check. -/
theorem fresh_slot_binding_acyclic :
    Acyclic (bind (bind (fun _ => none) "q" (.symbol "leaf")) "x" (.var "q")) :=
  (bind_frame_preserves
    (frame := fixtureFrame)
    (fun y u bound reach => by
      by_cases same : y = "q"
      · subst same
        rw [bind_self] at bound
        cases bound
        cases reach with
        | here member => simp [vars] at member
        | through member _ _ => simp [vars] at member
      · rw [bind_other _ _ same] at bound
        cases bound)
    outer_avoiding_write_keeps_fresh rfl
    (fun v member => by
      simp [vars] at member
      simp [fixtureFrame, member])).1

end Mettapedia.Languages.MeTTa.FreshFrameOccursCheck
