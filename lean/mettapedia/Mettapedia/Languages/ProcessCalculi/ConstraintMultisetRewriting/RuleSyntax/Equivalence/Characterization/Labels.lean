import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Instances

/-!
# Why minimal enabling contexts fail as labels for none queries

A labelled semantics whose labels are the *minimal* contexts that enable a firing (relative pushouts;
the least constraint that enables a move, in concurrent constraint programming) needs, for each firing,
a least enabling context. For a none query there is none at this instance.

The guarded spawn ("make `5` where no `9` is present") at one row labelled by the free unknown `x`:

* it does not fire there, since a solution may send `x` to `9`;
* the tell context `x = k` enables it, for every `k ≠ 9` (`enables_bound`);
* **every knowledge that both `x = 5` and `x = 6` entail fails to enable it** (`not_enables_of_entailed`):
  such a knowledge is solved by sending `x` to `9`, so the none query fails there;
* hence **no enabling tell context is entailed by every enabling one** (`no_least_enabling_tell`).

The reason is that the weakest enabling condition, "`x` is not `9`", is a disequation, and the knowledge
holds equations only. The label of such a firing must carry a negative part (what the context must not
make true), as the labels of borrowed contexts carry negative application conditions; a saturated
semantics, in which every enabling context is a label, has no such obstruction.

**The control: with an equation guard the least enabling tell exists.** The guarded read ("read a row,
check that it is `5`, make `7`") at the same row: the tell `x = 5` enables it (`enablesRead_five`), and
every enabling tell entails `x = 5` (`models_five_of_enablesRead`), since the opening is fresh and a
solution of the context extends to the opened read variable; hence a least enabling tell context
(`least_enabling_tell_read`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c fresh_of_ground)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong Moves rowX spawnGuarded spawnGuarded_fresh information_of_empty)

/-- **The tell context `L` enables the guarded spawn** at the row `x`. -/
def Enables (L : EquationStore (Term atoms)) : Prop := Moves ⟨{spawnGuarded}, tellState rowX L⟩

/-- The substitution that sends `x` to `k` and fixes every other unknown. -/
def pinX (k : ℕ) : Subst atoms := fun v => if v = 0 then c k else .var v

open Classical in
theorem applyTerm_pinX (k : ℕ) (t : Term atoms) :
    Subst.applyTerm (pinX k) t = if t = .var 0 then c k else t := by
  cases t with
  | var v =>
      by_cases zero : v = 0
      · subst zero
        rw [if_pos rfl]
        show (if (0 : ℕ) = 0 then c k else .var 0) = c k
        rw [if_pos rfl]
      · have other : (Term.var v : Term atoms) ≠ .var 0 := fun same => zero (Term.var.inj same)
        rw [if_neg other]
        show (if v = 0 then c k else .var v) = .var v
        rw [if_neg zero]
  | const n =>
      have other : (Term.const n : Term atoms) ≠ .var 0 := fun same => by cases same
      rw [if_neg other]
      rfl
  | app fn _ => exact nomatch fn

/-- An equation solved by sending `x` to `5` and by sending it to `6` is solved by sending it to `9`. -/
theorem solves_pinX_nine {e : Equation (Term atoms)}
    (five : Subst.applyTerm (pinX 5) e.1 = Subst.applyTerm (pinX 5) e.2)
    (six : Subst.applyTerm (pinX 6) e.1 = Subst.applyTerm (pinX 6) e.2) :
    Subst.applyTerm (pinX 9) e.1 = Subst.applyTerm (pinX 9) e.2 := by
  simp only [applyTerm_pinX] at five six ⊢
  by_cases left : e.1 = .var 0 <;> by_cases right : e.2 = .var 0
  · rw [if_pos left, if_pos right]
  · rw [if_pos left, if_neg right] at five six
    exact absurd (Term.const.inj (five.trans six.symm)) (by decide)
  · rw [if_neg left, if_pos right] at five six
    exact absurd (Term.const.inj (five.symm.trans six)) (by decide)
  · rw [if_neg left, if_neg right] at five ⊢
    exact five

/-- **The tell context `x = k` enables the guarded spawn**, for every `k ≠ 9`. -/
theorem enables_bound {k : ℕ} (different : k ≠ 9) : Enables [(x, c k)] := by
  let s := tellState rowX [(x, c k)]
  let f : Firing ℕ E ({spawnGuarded} : Program Tm) s.frame :=
    ⟨spawnGuarded, Set.mem_singleton _, PUnit.unit, Subst.id atoms, ⟨[], [], [1]⟩, []⟩
  have info : f.information X s = X.applyStore (a := PUnit.unit) (b := PUnit.unit)
      (E.weaken f.ext) s.knowledge := information_of_empty f rfl rfl rfl
  have admitted : f.Admits X s := by
    refine (admits_iff f).mpr ⟨spawnGuarded_fresh s f (Or.inl rfl),
      ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_,
      fun q inside => absurd inside List.not_mem_nil⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · simp [f, s, Selection.commit, tellState, rowX]
      · intro q inside
        simp [f, Selection.commit] at inside
    · rw [info]
      refine ⟨PUnit.unit, fun _ => c k, fun e inside => ?_⟩
      obtain ⟨e', member, rfl⟩ := List.mem_map.mp inside
      have isBound : e' = (x, c k) := by simpa [s, tellState, rowX] using member
      subst isBound
      rfl
    · intro check inside b τ solved
      have isNone : check = .predicate .none (c 9) := List.mem_singleton.mp inside
      subst isNone
      rw [info] at solved
      have bound : Subst.applyTerm τ (Subst.applyTerm (Subst.id atoms) x) =
          Subst.applyTerm τ (Subst.applyTerm (Subst.id atoms) (c k)) :=
        solved _ (List.mem_map.mpr ⟨(x, c k), by simp [s, tellState, rowX], rfl⟩)
      intro o _ equated
      have nine : Subst.applyTerm τ (c 9) =
          Subst.applyTerm τ (Subst.applyTerm (Subst.id atoms) x) := equated
      rw [bound] at nine
      exact different (Term.const.inj nine).symm
  exact ⟨_, reduces_of_admits f admitted⟩

/-- **Every knowledge that both `x = 5` and `x = 6` entail fails to enable the guarded spawn.** -/
theorem not_enables_of_entailed {L : EquationStore (Term atoms)}
    (five : X.Models (a := PUnit.unit) (b := PUnit.unit) (pinX 5) L)
    (six : X.Models (a := PUnit.unit) (b := PUnit.unit) (pinX 6) L) : ¬ Enables L := by
  rintro ⟨T, -, ⟨rule, member, ext, ι, selection, seen⟩, admitted, -⟩
  have isRule : rule = spawnGuarded := member
  subst isRule
  obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff _).mp admitted
  have info : (⟨spawnGuarded, member, ext, ι, selection, seen⟩ :
      Firing ℕ E ({spawnGuarded} : Program Tm) (tellState rowX L).frame).information X
        (tellState rowX L) = X.applyStore (a := PUnit.unit) (b := PUnit.unit) (E.weaken ext)
          (tellState rowX L).knowledge := information_of_empty _ rfl rfl rfl
  have nineSolves : X.Models (a := PUnit.unit) (b := PUnit.unit) (pinX 9)
      ((⟨spawnGuarded, member, ext, ι, selection, seen⟩ :
        Firing ℕ E ({spawnGuarded} : Program Tm) (tellState rowX L).frame).information X
          (tellState rowX L)) := by
    rw [info]
    intro e inside
    obtain ⟨e', member', rfl⟩ := List.mem_map.mp inside
    have inL : e' ∈ L := by simpa [tellState, rowX] using member'
    show Subst.applyTerm (pinX 9) (Subst.applyTerm (Subst.id atoms) e'.1) =
      Subst.applyTerm (pinX 9) (Subst.applyTerm (Subst.id atoms) e'.2)
    rw [Subst.applyTerm_id, Subst.applyTerm_id]
    exact solves_pinX_nine (five e' inL) (six e' inL)
  have holds := checks (.predicate .none (c 9)) (List.mem_singleton_self _) PUnit.unit (pinX 9) nineSolves
  apply holds 0 (Finset.mem_singleton_self 0)
  show Subst.applyTerm (pinX 9) (c 9) =
    Subst.applyTerm (pinX 9) (Subst.applyTerm (Subst.id atoms) x)
  rfl

/-- **No least enabling tell context**: no enabling knowledge is entailed by every enabling one. -/
theorem no_least_enabling_tell :
    ¬ ∃ L₀ : EquationStore (Term atoms), Enables L₀ ∧ ∀ L, Enables L →
      ∀ σ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) σ L →
        X.Models (a := PUnit.unit) (b := PUnit.unit) σ L₀ := by
  rintro ⟨L₀, enables, least⟩
  have five := least [(x, c 5)] (enables_bound (by decide)) (pinX 5)
    (fun e inside => by
      obtain rfl := List.mem_singleton.mp inside
      rfl)
  have six := least [(x, c 6)] (enables_bound (by decide)) (pinX 6)
    (fun e inside => by
      obtain rfl := List.mem_singleton.mp inside
      rfl)
  exact not_enables_of_entailed five six enables

/-! ## With an equation guard, the least enabling tell exists -/

/-- **The guarded read**: read a row, check that it is `5`, make `7`. Its guard is an equation. -/
def readFive : Rule Tm := ⟨PUnit.unit, ⟨[], [x], [], [.equal x (c 5)], [c 7]⟩, []⟩

/-- **The tell context `L` enables the guarded read** at the row `x`. -/
def EnablesRead (L : EquationStore (Term atoms)) : Prop := Moves ⟨{readFive}, tellState rowX L⟩

/-- **The tell context `x = 5` enables the guarded read.** -/
theorem enablesRead_five : EnablesRead [(x, c 5)] := by
  let s := tellState rowX [(x, c 5)]
  let f : Firing ℕ E ({readFive} : Program Tm) s.frame :=
    ⟨readFive, Set.mem_singleton _, PUnit.unit, fun v => .var (8 + v), ⟨[], [0], [1]⟩, []⟩
  have info : f.information X s = [(x, c 5), (.var 8, x)] := rfl
  have admitted : f.Admits X s := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_,
      ?_, ?_, fun q inside => absurd inside List.not_mem_nil⟩
    · refine fresh_shift f (N := 8) (fun t mentioned => ?_) fun v => rfl
      rcases mentioned with inside | inside | ⟨o, -, rfl⟩
      · have isX : t = x := by simpa [s, tellState, rowX] using inside
        subst isX
        decide
      · have isFive : t = c 5 := by simpa [s, tellState, rowX] using inside
        subst isFive
        decide
      · show size x ≤ 8
        decide
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [f, Selection.commit]
      · simp [f, s, Selection.commit, tellState, rowX]
      · simp [f, Selection.commit]
      · simp [f, s, Selection.commit, tellState, rowX]
      · intro q inside
        simp [f, Selection.commit] at inside
    · rw [info]
      refine ⟨PUnit.unit, fun _ => c 5, fun e inside => ?_⟩
      rcases List.mem_cons.mp inside with same | inside
      · subst same
        rfl
      · rw [List.mem_singleton] at inside
        subst inside
        rfl
    · intro check inside b τ solved
      rw [info] at solved
      have isEqual : check = .equal (.var 8) (c 5) := List.mem_singleton.mp inside
      subst isEqual
      have five : Subst.applyTerm τ x = Subst.applyTerm τ (c 5) := solved (x, c 5) (by simp)
      have read : Subst.applyTerm τ (.var 8) = Subst.applyTerm τ x := solved (.var 8, x) (by simp)
      show Subst.applyTerm τ (.var 8) = Subst.applyTerm τ (c 5)
      rw [read, five]
  exact ⟨_, reduces_of_admits f admitted⟩

/-- **Every tell context that enables the guarded read entails `x = 5`.** The firing's opening is
fresh, so a solution of the context extends to the opened read variable, sent where `x` is sent; it
solves the firing's information, so the guard holds there. -/
theorem models_five_of_enablesRead {L : EquationStore (Term atoms)} (enables : EnablesRead L)
    (σ : Subst atoms) (solves : X.Models (a := PUnit.unit) (b := PUnit.unit) σ L) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) σ [(x, c 5)] := by
  obtain ⟨T, -, ⟨rule, member, ext, ι, ⟨taken, read, made⟩, seen⟩, admitted, -⟩ := enables
  have isRule : rule = readFive := member
  subst isRule
  obtain ⟨fresh, ⟨-, -, -, readLength, -, -⟩, -, -, checks, -⟩ := (admits_iff _).mp admitted
  obtain ⟨o, rest, rfl⟩ : ∃ o rest, read = o :: rest := by
    cases read with
    | nil => exact absurd readLength (by simp [readFive])
    | cons o rest => exact ⟨o, rest, rfl⟩
  obtain ⟨u, onState, onRule⟩ := fresh PUnit.unit σ (fun _ => Subst.applyTerm σ x)
  have onState' : ∀ t, (tellState rowX L).Mentions t →
      Subst.applyTerm u (Subst.applyTerm (Subst.id atoms) t) = Subst.applyTerm σ t := onState
  have uX : Subst.applyTerm u x = Subst.applyTerm σ x := by
    have mentioned := onState' x (Or.inr (Or.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩))
    rwa [Subst.applyTerm_id] at mentioned
  have uRead : Subst.applyTerm u (Subst.applyTerm ι x) = Subst.applyTerm σ x :=
    onRule x (by simp [readFive, Rule.terms])
  have uSolves : ∀ e ∈ (⟨readFive, member, ext, ι, ⟨taken, o :: rest, made⟩, seen⟩ :
      Firing ℕ E ({readFive} : Program Tm) (tellState rowX L).frame).information X (tellState rowX L),
      Subst.applyTerm u e.1 = Subst.applyTerm u e.2 := by
    intro e inside
    have unfolded : e ∈ X.applyStore (a := PUnit.unit) (b := PUnit.unit) (E.weaken ext)
        (tellState rowX L).knowledge ++ [] ++
        [(Subst.applyTerm ι x, Subst.applyTerm (Subst.id atoms) x)] ++ [] := inside
    simp only [List.append_nil, List.mem_append, List.mem_singleton] at unfolded
    rcases unfolded with known | matched
    · obtain ⟨e', member', rfl⟩ := List.mem_map.mp known
      have inL : e' ∈ L := by simpa [tellState, rowX] using member'
      show Subst.applyTerm u (Subst.applyTerm (Subst.id atoms) e'.1) =
        Subst.applyTerm u (Subst.applyTerm (Subst.id atoms) e'.2)
      rw [onState' e'.1 (Or.inl (List.mem_map.mpr ⟨e', member', rfl⟩)),
        onState' e'.2 (Or.inr (Or.inl (List.mem_map.mpr ⟨e', member', rfl⟩)))]
      exact solves e' inL
    · subst matched
      show Subst.applyTerm u (Subst.applyTerm ι x) =
        Subst.applyTerm u (Subst.applyTerm (Subst.id atoms) x)
      rw [uRead, Subst.applyTerm_id, uX]
  have guard : Subst.applyTerm u (Subst.applyTerm ι x) = Subst.applyTerm u (c 5) :=
    checks (.equal (Subst.applyTerm ι x) (c 5)) (List.mem_singleton_self _) PUnit.unit u uSolves
  intro e inside
  obtain rfl := List.mem_singleton.mp inside
  show Subst.applyTerm σ x = Subst.applyTerm σ (c 5)
  rw [← uRead]
  exact guard

/-- **The least enabling tell context exists for the guarded read**: `x = 5` enables it, and every
enabling tell context entails it. -/
theorem least_enabling_tell_read :
    ∃ L₀ : EquationStore (Term atoms), EnablesRead L₀ ∧ ∀ L, EnablesRead L →
      ∀ σ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) σ L →
        X.Models (a := PUnit.unit) (b := PUnit.unit) σ L₀ :=
  ⟨[(x, c 5)], enablesRead_five, fun _ enables σ solves => models_five_of_enablesRead enables σ solves⟩

#print axioms applyTerm_pinX
#print axioms solves_pinX_nine
#print axioms enables_bound
#print axioms not_enables_of_entailed
#print axioms no_least_enabling_tell
#print axioms enablesRead_five
#print axioms models_five_of_enablesRead
#print axioms least_enabling_tell_read

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization
