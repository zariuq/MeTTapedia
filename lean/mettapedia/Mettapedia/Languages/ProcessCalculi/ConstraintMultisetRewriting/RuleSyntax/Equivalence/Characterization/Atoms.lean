import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.TellReadControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.GuardTerms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Standard

/-!
# Tools for characterizing the congruence: unsolvable systems, and first-order atoms at one frame

## Unsolvable systems (every frame action)

* A system whose knowledge is unsolvable does not move (`stuck_of_unsolvable`): a firing's information
  carries the knowledge along its extension.
* **All systems with unsolvable knowledge are congruent** (`unsolvable_congruent`), whatever their
  programs and rows, for barbs that no unsolvable state shows and infinitely many identities: no move,
  no barb, and every context keeps the knowledge unsolvable.

## One frame, first-order atoms (`Equivalence.AtOneFrame`)

Every term is an unknown or a constant.

* **Bounds** (`size`, `sizeBound`, `stateBound`): every numeral of a listed term lies below the bound.
* **Grounding** (`groundAt N`: each unknown `v` to the constant `N + v`) is injective on terms whose
  constants lie below `N` (`groundAt_injective`), and a substitution followed by it has constant values
  (`isConst_applyTerm_grounded`), so it is a solution of every store `pin` tells (`models_pin_self`).
* **Exchanging two constants** (`swapConst`, `swapSubst`) keeps the solutions of a store that mentions
  neither (`models_swapSubst`). Hence a state that mentions neither constant shows the may-barb of the
  one exactly when it shows the may-barb of the other (`mayBarb_swap`): an unused constant cannot be
  told from another. A firing of a rule that avoids a constant, at a state that avoids it, has a result
  that avoids it (`result_avoids`): a fresh opening sends a rule's unknowns to unknowns
  (`opening_var`).
* **Fresh openings exist** above every unknown the state mentions (`fresh_shift`), and a rule with one
  unknown may be opened as any unknown the state does not mention (`fresh_at`).
* The rule that does nothing moves at every state with solvable knowledge (`idle_moves`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

universe uO uT uH uE uOcc uB

/-! ## Unsolvable systems, at every frame action -/

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}

/-- The knowledge of the state at which a firing is admitted is solvable. -/
theorem solvable_of_admits {P : Program Tm} {s : State Tm O} {f : Firing O E P s.frame}
    (admitted : f.Admits X s) : X.Solvable s.knowledge :=
  Frames.solvable_of_applyStore (E.weaken f.ext)
    (Frames.solvable_of_subset (fun _ member => List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ member))) admitted.2.2.1)

/-- **A system with unsolvable knowledge does not move.** -/
theorem stuck_of_unsolvable {S : System Tm O} (unsolvable : ¬ X.Solvable S.state.knowledge) :
    ¬ ∃ T, Reduces X O E S T := by
  rintro ⟨T, -, f, admitted, -⟩
  exact unsolvable (solvable_of_admits admitted)

/-- **All systems with unsolvable knowledge are congruent**, whatever their programs and rows, for
barbs that no unsolvable state shows, with infinitely many identities. -/
theorem unsolvable_congruent [Infinite O] {B : Type uB} {obs : B → State Tm O → Prop}
    (noBarb : ∀ β (s : State Tm O), ¬ X.Solvable s.knowledge → ¬ obs β s)
    {S T : System Tm O} (unsolvableS : ¬ X.Solvable S.state.knowledge)
    (unsolvableT : ¬ X.Solvable T.state.knowledge) : Congruent X O E obs S T := by
  let R : System Tm O → System Tm O → Prop := fun S T =>
    ¬ X.Solvable S.state.knowledge ∧ ¬ X.Solvable T.state.knowledge
  have candidate : Candidate X O E obs R := {
    symm := fun ⟨one, two⟩ => ⟨two, one⟩
    barbs := fun ⟨one, _⟩ β holds => absurd holds (noBarb β _ one)
    reduces := fun ⟨one, _⟩ _ moved => absurd ⟨_, moved⟩ (stuck_of_unsolvable one)
    context := by
      rintro S T ⟨one, two⟩ c applies
      cases c with
      | rows ids label =>
          obtain ⟨π, apart⟩ := exists_perm_avoid T.state.present ids
          exact ⟨π, apart, one, two⟩
      | rules added => exact ⟨1, Basic.applies_of_ids_empty rfl _, one, two⟩
      | tell equations =>
          refine ⟨1, Basic.applies_of_ids_empty rfl _, fun solvable => one ?_,
            fun solvable => two ?_⟩
          · exact Frames.solvable_of_subset (fun e member => List.mem_append_left _ member) solvable
          · exact Frames.solvable_of_subset (fun e member => List.mem_append_left _ member) solvable
      | extend extension =>
          exact ⟨1, Basic.applies_of_ids_empty rfl _,
            fun solvable => one (Frames.solvable_of_applyStore _ solvable),
            fun solvable => two (Frames.solvable_of_applyStore _ solvable)⟩ }
  exact candidate.le_congruent ⟨unsolvableS, unsolvableT⟩

end General

/-! ## One frame, first-order atoms -/

section OneFrame

open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c fresh_of_ground)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong Moves pat idle information_of_empty)

/-! ### Bounds -/

/-- One more than the numeral of a term, its unknown or its constant. -/
def size : Term atoms → ℕ
  | .var v => v + 1
  | .const n => n + 1
  | .app f _ => nomatch f

/-- A bound above the numerals of every term of a list. -/
def sizeBound (terms : List (Term atoms)) : ℕ := (terms.map size).sum

theorem size_le_sizeBound {terms : List (Term atoms)} {t : Term atoms} (inside : t ∈ terms) :
    size t ≤ sizeBound terms :=
  List.le_sum_of_mem (List.mem_map_of_mem inside)

/-- The terms a state mentions, listed: the sides of its knowledge and the labels of its rows. -/
noncomputable def mentioned (s : State Tm ℕ) : List (Term atoms) :=
  s.knowledge.map Prod.fst ++ s.knowledge.map Prod.snd ++ s.present.toList.map s.label

theorem mem_mentioned {s : State Tm ℕ} {t : Term atoms} : t ∈ mentioned s ↔ s.Mentions t := by
  unfold mentioned State.Mentions
  simp only [List.mem_append, List.mem_map, Finset.mem_toList, or_assoc]

/-- A bound above every numeral a state mentions. -/
noncomputable def stateBound (s : State Tm ℕ) : ℕ := sizeBound (mentioned s)

theorem size_le_stateBound {s : State Tm ℕ} {t : Term atoms} (mentions : s.Mentions t) :
    size t ≤ stateBound s :=
  size_le_sizeBound (mem_mentioned.mpr mentions)

/-! ### Grounding -/

/-- A term is a constant. -/
def IsConst (t : Term atoms) : Prop := ∃ k, t = .const k

theorem applyTerm_of_isConst (τ : Subst atoms) {t : Term atoms} (constant : IsConst t) :
    Subst.applyTerm τ t = t := by
  obtain ⟨k, rfl⟩ := constant
  rfl

/-- **Grounding above `N`**: each unknown `v` to the constant `N + v`. -/
def groundAt (N : ℕ) : Subst atoms := fun v => .const (N + v)

theorem isConst_applyTerm_groundAt (N : ℕ) (t : Term atoms) :
    IsConst (Subst.applyTerm (groundAt N) t) := by
  cases t with
  | var v => exact ⟨N + v, rfl⟩
  | const k => exact ⟨k, rfl⟩
  | app f _ => exact nomatch f

/-- **Grounding is injective on terms whose constants lie below the bound.** -/
theorem groundAt_injective {N : ℕ} {t u : Term atoms} (smallT : size t ≤ N) (smallU : size u ≤ N)
    (same : Subst.applyTerm (groundAt N) t = Subst.applyTerm (groundAt N) u) : t = u := by
  cases t with
  | var v =>
      cases u with
      | var w =>
          have values : N + v = N + w := Term.const.inj same
          rw [Nat.add_left_cancel values]
      | const k =>
          have values : N + v = k := Term.const.inj same
          simp only [size] at smallU
          omega
      | app f _ => exact nomatch f
  | const k =>
      cases u with
      | var w =>
          have values : N + w = k := (Term.const.inj same).symm
          simp only [size] at smallT
          omega
      | const k' => exact congrArg Term.const (Term.const.inj same)
      | app f _ => exact nomatch f
  | app f _ => exact nomatch f

/-- A substitution followed by grounding has constant values. -/
theorem isConst_applyTerm_grounded (N : ℕ) (σ : Subst atoms) (t : Term atoms) :
    IsConst (Subst.applyTerm (Subst.comp (groundAt N) σ) t) := by
  rw [Subst.applyTerm_comp]
  exact isConst_applyTerm_groundAt N _

/-- **Pinning**: tell each listed term its value under `σ`. -/
def pin (σ : Subst atoms) (terms : List (Term atoms)) : EquationStore (Term atoms) :=
  terms.map fun t => (t, Subst.applyTerm σ t)

/-- A solution of a pinning agrees with `σ` on the pinned terms, when `σ`'s values there are
constants. -/
theorem models_pin_iff {σ : Subst atoms} {terms : List (Term atoms)}
    (constant : ∀ t ∈ terms, IsConst (Subst.applyTerm σ t)) (τ : Subst atoms) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) τ (pin σ terms) ↔
      ∀ t ∈ terms, Subst.applyTerm τ t = Subst.applyTerm σ t := by
  constructor
  · intro solved t inside
    have equated : Subst.applyTerm τ t = Subst.applyTerm τ (Subst.applyTerm σ t) :=
      solved (t, Subst.applyTerm σ t) (List.mem_map.mpr ⟨t, inside, rfl⟩)
    rw [applyTerm_of_isConst τ (constant t inside)] at equated
    exact equated
  · intro agree e member
    obtain ⟨t, inside, rfl⟩ := List.mem_map.mp member
    show Subst.applyTerm τ t = Subst.applyTerm τ (Subst.applyTerm σ t)
    rw [applyTerm_of_isConst τ (constant t inside)]
    exact agree t inside

/-- A substitution with constant values on the pinned terms solves its own pinning. -/
theorem models_pin_self {σ : Subst atoms} {terms : List (Term atoms)}
    (constant : ∀ t ∈ terms, IsConst (Subst.applyTerm σ t)) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) σ (pin σ terms) :=
  (models_pin_iff constant σ).mpr fun _ _ => rfl

/-! ### Exchanging two constants -/

/-- **Exchange the constants `z` and `z'`** in a term. -/
def swapConst (z z' : ℕ) : Term atoms → Term atoms
  | .var v => .var v
  | .const n => .const (Equiv.swap z z' n)
  | .app f _ => nomatch f

/-- A substitution followed by the exchange. -/
def swapSubst (z z' : ℕ) (σ : Subst atoms) : Subst atoms := fun v => swapConst z z' (σ v)

theorem applyTerm_swapSubst {z z' : ℕ} (σ : Subst atoms) {t : Term atoms} (notZ : t ≠ .const z)
    (notZ' : t ≠ .const z') :
    Subst.applyTerm (swapSubst z z' σ) t = swapConst z z' (Subst.applyTerm σ t) := by
  cases t with
  | var v => rfl
  | const n =>
      have one : n ≠ z := fun same => notZ (congrArg Term.const same)
      have two : n ≠ z' := fun same => notZ' (congrArg Term.const same)
      show (Term.const n : Term atoms) = Term.const (Equiv.swap z z' n)
      rw [Equiv.swap_apply_of_ne_of_ne one two]
  | app f _ => exact nomatch f

/-- A state avoids a constant: it mentions no term equal to it. -/
def Avoids (z : ℕ) (s : State Tm ℕ) : Prop := ∀ t, s.Mentions t → t ≠ .const z

/-- **The exchange keeps the solutions** of a knowledge that mentions neither constant. -/
theorem models_swapSubst {z z' : ℕ} {s : State Tm ℕ} (avoidsZ : Avoids z s) (avoidsZ' : Avoids z' s)
    {σ : Subst atoms} (solved : X.Models (a := PUnit.unit) (b := PUnit.unit) σ s.knowledge) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) (swapSubst z z' σ) s.knowledge := by
  intro e member
  have left : s.Mentions e.1 := Or.inl (List.mem_map_of_mem member)
  have right : s.Mentions e.2 := Or.inr (Or.inl (List.mem_map_of_mem member))
  have equated : Subst.applyTerm σ e.1 = Subst.applyTerm σ e.2 := solved e member
  show Subst.applyTerm (swapSubst z z' σ) e.1 = Subst.applyTerm (swapSubst z z' σ) e.2
  rw [applyTerm_swapSubst σ (avoidsZ _ left) (avoidsZ' _ left),
    applyTerm_swapSubst σ (avoidsZ _ right) (avoidsZ' _ right), equated]

/-- **An unused constant cannot be told from another**: a state that mentions neither shows the
may-barb of the one exactly when it shows the may-barb of the other. -/
theorem mayBarb_swap {z z' : ℕ} {s : State Tm ℕ} (avoidsZ : Avoids z s) (avoidsZ' : Avoids z' s)
    (barb : MayBarb X (pat (c z)) s) : MayBarb X (pat (c z')) s := by
  obtain ⟨o, present, b, σ, h, known, equated⟩ := barb
  have mentions : s.Mentions (s.label o) := Or.inr (Or.inr ⟨o, present, rfl⟩)
  have value : Subst.applyTerm σ (s.label o) = c z := equated
  refine ⟨o, present, PUnit.unit, swapSubst z z' σ, Subst.id atoms,
    models_swapSubst avoidsZ avoidsZ' known, ?_⟩
  show Subst.applyTerm (swapSubst z z' σ) (s.label o) = c z'
  rw [applyTerm_swapSubst σ (avoidsZ _ mentions) (avoidsZ' _ mentions), value]
  show (Term.const (Equiv.swap z z' z) : Term atoms) = Term.const z'
  rw [Equiv.swap_apply_left]

/-! ### Fresh openings -/

/-- **A fresh opening sends each unknown of its rule to an unknown the state does not mention.** -/
theorem opening_var {P : Program Tm} {s : State Tm ℕ} (f : Firing ℕ E P s.frame) (fresh : f.Fresh X s)
    {v : ℕ} (term : (Term.var v : Term atoms) ∈ f.rule.terms) :
    ∃ w, f.opening v = .var w ∧ ¬ s.Mentions (.var w) := by
  obtain ⟨u, state, rule⟩ := fresh PUnit.unit (fun _ => c 0) (fun _ => c 1)
  obtain ⟨u', -, rule'⟩ := fresh PUnit.unit (fun _ => c 0) (fun _ => c 2)
  have one : Subst.applyTerm u (f.opening v) = c 1 := rule _ term
  have two : Subst.applyTerm u' (f.opening v) = c 2 := rule' _ term
  cases opened : f.opening v with
  | var w =>
      refine ⟨w, rfl, fun mentions => ?_⟩
      have seen : u w = c 0 := state (.var w) mentions
      rw [opened] at one
      have bad : (c 0 : Term atoms) = c 1 := seen.symm.trans one
      exact absurd (Term.const.inj bad) (by decide)
  | const k =>
      rw [opened] at one two
      exact absurd ((Term.const.inj one).symm.trans (Term.const.inj two)) (by decide)
  | app fn _ => exact nomatch fn

/-- An opened term of the rule avoids every constant the rule's term avoids. -/
theorem opened_ne {P : Program Tm} {s : State Tm ℕ} (f : Firing ℕ E P s.frame) (fresh : f.Fresh X s)
    {t : Term atoms} (term : t ∈ f.rule.terms) {z : ℕ} (notZ : t ≠ .const z) :
    Subst.applyTerm f.opening t ≠ .const z := by
  cases t with
  | var v =>
      obtain ⟨w, opened, -⟩ := opening_var f fresh term
      show f.opening v ≠ .const z
      rw [opened]
      exact fun same => by cases same
  | const n => exact notZ
  | app fn _ => exact nomatch fn

/-- **The shifted opening is fresh**: each unknown `v` of the rule to `N + v`, above every unknown the
state mentions. -/
theorem fresh_shift {P : Program Tm} {s : State Tm ℕ} (f : Firing ℕ E P s.frame) {N : ℕ}
    (above : ∀ t, s.Mentions t → size t ≤ N) (shifted : ∀ v, f.opening v = .var (N + v)) :
    f.Fresh X s := by
  intro b g h
  refine ⟨fun w => if N ≤ w then h (w - N) else g w, fun t mentions => ?_, fun t _ => ?_⟩
  · show Subst.applyTerm (fun w => if N ≤ w then h (w - N) else g w)
      (Subst.applyTerm (Subst.id atoms) t) = Subst.applyTerm g t
    rw [Subst.applyTerm_id]
    cases t with
    | var w =>
        have small := above _ mentions
        simp only [size] at small
        have below : ¬ N ≤ w := by omega
        show (if N ≤ w then h (w - N) else g w) = g w
        rw [if_neg below]
    | const _ => rfl
    | app fn _ => exact nomatch fn
  · show Subst.applyTerm (fun w => if N ≤ w then h (w - N) else g w)
      (Subst.applyTerm f.opening t) = Subst.applyTerm h t
    cases t with
    | var v =>
        show Subst.applyTerm (fun w => if N ≤ w then h (w - N) else g w) (f.opening v) = h v
        rw [shifted v]
        show (if N ≤ N + v then h (N + v - N) else g (N + v)) = h v
        rw [if_pos (Nat.le_add_right N v), Nat.add_sub_cancel_left]
    | const _ => rfl
    | app fn _ => exact nomatch fn

/-- **A rule whose only unknown is `0` may be opened as any unknown the state does not mention.** -/
theorem fresh_at {P : Program Tm} {s : State Tm ℕ} (f : Firing ℕ E P s.frame) {w : ℕ}
    (unmentioned : ¬ s.Mentions (.var w))
    (only : ∀ v, (Term.var v : Term atoms) ∈ f.rule.terms → v = 0) (opened : f.opening 0 = .var w) :
    f.Fresh X s := by
  intro b g h
  refine ⟨fun v => if v = w then h 0 else g v, fun t mentions => ?_, fun t inside => ?_⟩
  · show Subst.applyTerm (fun v => if v = w then h 0 else g v)
      (Subst.applyTerm (Subst.id atoms) t) = Subst.applyTerm g t
    rw [Subst.applyTerm_id]
    cases t with
    | var v =>
        have other : v ≠ w := fun same => unmentioned (same ▸ mentions)
        show (if v = w then h 0 else g v) = g v
        rw [if_neg other]
    | const _ => rfl
    | app fn _ => exact nomatch fn
  · show Subst.applyTerm (fun v => if v = w then h 0 else g v)
      (Subst.applyTerm f.opening t) = Subst.applyTerm h t
    cases t with
    | var v =>
        have zero : v = 0 := only v inside
        subst zero
        show Subst.applyTerm (fun v => if v = w then h 0 else g v) (f.opening 0) = h 0
        rw [opened]
        show (if w = w then h 0 else g w) = h 0
        rw [if_pos rfl]
    | const _ => rfl
    | app fn _ => exact nomatch fn

/-! ### Results that avoid a constant -/

/-- **A firing of a rule that avoids a constant, at a state that avoids it, has a result that avoids
it.** -/
theorem result_avoids {P : Program Tm} {s : State Tm ℕ} (f : Firing ℕ E P s.frame)
    (admitted : f.Admits X s) {z : ℕ} (rule : ∀ t ∈ f.rule.terms, t ≠ .const z)
    (state : Avoids z s) : Avoids z (f.result X s) := by
  obtain ⟨fresh, -, -, -, -, produceLength, -⟩ := admitted.1
  have enabled := admitted.2.1
  have takenPresent : ∀ o ∈ f.selection.taken, o ∈ s.present := fun o member =>
    enabled.taken_subset (by simpa [Selection.commit] using member)
  have readPresent : ∀ o ∈ f.selection.read, o ∈ s.present := fun o member =>
    enabled.kept_subset (by simpa [Selection.commit] using member)
  have rowAvoids : ∀ o ∈ s.present, f.row X s o ≠ .const z := fun o present => by
    show Subst.applyTerm (Subst.id atoms) (s.label o) ≠ .const z
    rw [Subst.applyTerm_id]
    exact state _ (Or.inr (Or.inr ⟨o, present, rfl⟩))
  have openedAvoids : ∀ t ∈ f.rule.terms, Subst.applyTerm f.opening t ≠ .const z := fun t inside =>
    opened_ne f fresh inside (rule t inside)
  have takeTerm : ∀ p ∈ (f.opened X).take, p ≠ .const z := by
    intro p inside
    obtain ⟨q, member, rfl⟩ := List.mem_map.mp inside
    exact openedAvoids q (AtOneFrame.mem_terms (Or.inl member))
  have readTerm : ∀ p ∈ (f.opened X).read, p ≠ .const z := by
    intro p inside
    obtain ⟨q, member, rfl⟩ := List.mem_map.mp inside
    exact openedAvoids q (AtOneFrame.mem_terms (Or.inr (Or.inl member)))
  have tellTerm : ∀ e ∈ (f.opened X).tell, e.1 ≠ .const z ∧ e.2 ≠ .const z := by
    intro e inside
    obtain ⟨e', member, rfl⟩ := List.mem_map.mp inside
    exact ⟨openedAvoids _ (AtOneFrame.mem_terms (Or.inr (Or.inr (Or.inl (List.mem_map_of_mem member))))),
      openedAvoids _ (AtOneFrame.mem_terms (Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_map_of_mem member))))))⟩
  have produceTerm : ∀ p ∈ (f.opened X).produce, p ≠ .const z := by
    intro p inside
    obtain ⟨q, member, rfl⟩ := List.mem_map.mp inside
    exact openedAvoids q (AtOneFrame.mem_terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl member)))))))
  -- Every equation of the information avoids the constant on both sides.
  have infoAvoids : ∀ e ∈ f.information X s, e.1 ≠ .const z ∧ e.2 ≠ .const z := by
    intro e inside
    rcases (mem_information f).mp inside with old | take | read | told
    · obtain ⟨e', member, rfl⟩ := List.mem_map.mp old
      show Subst.applyTerm (Subst.id atoms) e'.1 ≠ .const z ∧
        Subst.applyTerm (Subst.id atoms) e'.2 ≠ .const z
      rw [Subst.applyTerm_id, Subst.applyTerm_id]
      exact ⟨state _ (Or.inl (List.mem_map_of_mem member)),
        state _ (Or.inr (Or.inl (List.mem_map_of_mem member)))⟩
    · obtain ⟨p, o, paired, rfl⟩ := (mem_matching f).mp take
      exact ⟨takeTerm p (List.of_mem_zip paired).1,
        rowAvoids o (takenPresent o (List.of_mem_zip paired).2)⟩
    · obtain ⟨p, o, paired, rfl⟩ := (mem_matching f).mp read
      exact ⟨readTerm p (List.of_mem_zip paired).1,
        rowAvoids o (readPresent o (List.of_mem_zip paired).2)⟩
    · exact tellTerm e told
  have produceLength' : f.selection.made.length = (f.opened X).produce.length := by
    rw [← produceLength]
    exact (List.length_map _).symm
  rintro t (inFst | inSnd | ⟨o, present, rfl⟩)
  · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inFst
    exact (infoAvoids e inside).1
  · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inSnd
    exact (infoAvoids e inside).2
  · by_cases made : o ∈ f.selection.made
    · exact produceTerm _ (relabel_mem (f.row X s) _ _ o produceLength' made)
    · have old : o ∈ s.present := by
        rcases mem_fire.mp present with ⟨old, -⟩ | isMade
        · exact old
        · exact absurd (by simpa [Selection.commit] using isMade) made
      show relabel (f.row X s) f.selection.made (f.opened X).produce o ≠ .const z
      rw [Firing.relabel_of_not_mem (f.row X s) _ _ made]
      exact rowAvoids o old

/-! ### The rule that does nothing moves -/

/-- **The rule that does nothing moves at every state with solvable knowledge.** -/
theorem idle_moves {P : Program Tm} (member : idle ∈ P) (s : State Tm ℕ)
    (solvable : X.Solvable s.knowledge) : Moves ⟨P, s⟩ := by
  let f : Firing ℕ E P s.frame := ⟨idle, member, PUnit.unit, Subst.id atoms, ⟨[], [], []⟩, []⟩
  have admitted : f.Admits X s := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_,
      fun check inside => absurd inside List.not_mem_nil,
      fun q inside => absurd inside List.not_mem_nil⟩
    · apply fresh_of_ground action s f
      intro t member
      simp [f, idle, Rule.terms] at member
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · intro q inside
        simp [f, Selection.commit] at inside
    · rw [information_of_empty f rfl rfl rfl]
      obtain ⟨b, σ, solved⟩ := solvable
      refine ⟨b, σ, (Frames.models_applyStore _ _ _).mpr ?_⟩
      exact (Frames.models_congr (fun t => Frames.act_comp_id (X := X) σ t) s.knowledge).mp solved
  exact ⟨_, reduces_of_admits f admitted⟩

/-- **Systems with unsolvable knowledge are congruent at one frame.** -/
theorem unsolvable_cong {S T : Sys} (unsolvableS : ¬ X.Solvable S.state.knowledge)
    (unsolvableT : ¬ X.Solvable T.state.knowledge) : Cong S T :=
  unsolvable_congruent (fun _ _ unsolvable => not_mayBarb_of_unsolvable unsolvable) unsolvableS
    unsolvableT

end OneFrame

#print axioms solvable_of_admits
#print axioms stuck_of_unsolvable
#print axioms unsolvable_congruent
#print axioms mem_mentioned
#print axioms groundAt_injective
#print axioms isConst_applyTerm_grounded
#print axioms models_pin_iff
#print axioms models_pin_self
#print axioms applyTerm_swapSubst
#print axioms models_swapSubst
#print axioms mayBarb_swap
#print axioms opening_var
#print axioms opened_ne
#print axioms fresh_shift
#print axioms fresh_at
#print axioms result_avoids
#print axioms idle_moves
#print axioms unsolvable_cong

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization
