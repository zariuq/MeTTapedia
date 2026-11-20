import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Separations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.ProgramLaws
import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# Law 5 and the terms of the guard: which frames need which hypothesis

`entailedGuard_congruent` drops an equation guard that the rule's tells entail, when both terms of the
guard are terms of the rule; it holds at every frame action. That hypothesis is about freshness: an
opening is fresh on every term of its rule, so a guard whose terms are new asks the opening to send
their unknowns apart from what the state mentions. Whether that costs anything depends on the frame's
supply of unknowns apart from the state's.

* **At one frame over first-order terms with the numbers as unknowns, with function symbols or
  without, it is not needed** (`AtFirstOrder.entailedGuard_congruent_firstOrder`, for every set of
  constants and every set of function symbols with arities): an entailed guard may be dropped whatever
  its terms, beside every program, at every state, for every barb family. A firing of the rule without
  the guard is answered by the firing of the guarded rule whose opening keeps the image of every
  unknown that occurs in a term of the rule and sends every other unknown `v` to `N + v`, above every
  unknown the state and the old opening mention (`AtFirstOrder.reopen`). That opening opens the rule as
  before, and it is fresh for the guard's terms too: an unknown of the guard that occurs in a term of
  the rule is realized by the old opening's freshness, since first-order terms are free and two
  substitutions that send a term to the same term agree on its unknowns
  (`AtFirstOrder.agree_of_applyTerm_eq`); any other unknown of the guard is new. The guard holds at
  every solution because the tells entail it, and guards are not kept in the result: the two results
  are equal. An instance with a function symbol, whose guard's terms are not terms of the rule and
  carry an unknown the rule does not have: `AtFirstOrder.pair_guard_example`. The flat signature of
  `RuleSyntax.Examples` is the case with no function symbols (`AtFirstOrder.flat_instance`), where the
  same law was proved first (`AtOneFrame.entailedGuard_congruent_oneFrame`).
* **At one frame with one unknown the law fails without it** (`AtOneUnknown.guard_terms_needed`): the
  guard `v = v`, a tautology, is entailed by the tells of the rule that makes `5`, its term is not a
  term of that rule, and the guarded rule fires at no state that mentions `v`
  (`AtOneUnknown.guarded_stuck`), while the rule without the guard fires there
  (`AtOneUnknown.make_moves`). What that frame lacks is a supply of fresh unknowns: no rule that has
  the unknown among its terms has a fresh opening at a state that mentions it, guard or no guard
  (`AtOneUnknown.not_fresh_of_mentioned`); the rule that reads any row and makes `5`, which has no
  guard, does not move at the row `v` and moves at the row `7` (`AtOneUnknown.fresh_supply_needed`).
  The guard `v = v` only makes `v` a term of the rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtOneFrame

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c fresh_of_ground)
open RuleSyntax.Controls (atoms action)

/-! ## Unknowns below a bound -/

/-- One more than the unknown of a term, if it has one: the unknowns of the term lie below it. -/
def above : Term atoms → ℕ
  | .var v => v + 1
  | .const _ => 0
  | .app f _ => nomatch f

/-- A bound above the unknowns of every term of a list. -/
def bound (terms : List (Term atoms)) : ℕ := (terms.map above).sum

theorem above_le_bound {terms : List (Term atoms)} {t : Term atoms} (inside : t ∈ terms) :
    above t ≤ bound terms :=
  List.le_sum_of_mem (List.mem_map_of_mem inside)

/-- Substitutions that agree below a bound agree on every term whose unknowns lie below it. -/
theorem applyTerm_agree {σ τ : Subst atoms} {N : ℕ} (agree : ∀ v, v < N → σ v = τ v)
    {t : Term atoms} (below : above t ≤ N) : Subst.applyTerm σ t = Subst.applyTerm τ t := by
  cases t with
  | var v => exact agree v below
  | const _ => rfl
  | app f _ => exact nomatch f

/-! ## Re-opening a rule apart -/

/-- Every term of a rule, by where it occurs. -/
theorem mem_terms {r : Rule Tm} {t : Term atoms}
    (inside : t ∈ r.body.take ∨ t ∈ r.body.read ∨ t ∈ r.body.tell.map Prod.fst ∨
      t ∈ r.body.tell.map Prod.snd ∨ t ∈ r.body.checks.flatMap checkTerms ∨ t ∈ r.body.produce ∨
      t ∈ r.collect) : t ∈ r.terms := by
  unfold Rule.terms
  simp only [List.mem_append]
  tauto

/-- **Substitutions that agree on the terms of a rule open it alike**: its body and its collect query. -/
theorem map_congr_terms (r : Rule Tm) {σ τ : Subst atoms}
    (agree : ∀ t ∈ r.terms, Subst.applyTerm σ t = Subst.applyTerm τ t) :
    r.body.map (Subst.applyTerm σ) = r.body.map (Subst.applyTerm τ) ∧
      r.collect.map (Subst.applyTerm σ) = r.collect.map (Subst.applyTerm τ) := by
  have collect : r.collect.map (Subst.applyTerm σ) = r.collect.map (Subst.applyTerm τ) :=
    List.map_congr_left fun t inside =>
      agree t (mem_terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr inside)))))))
  refine ⟨?_, collect⟩
  have take : r.body.take.map (Subst.applyTerm σ) = r.body.take.map (Subst.applyTerm τ) :=
    List.map_congr_left fun t inside => agree t (mem_terms (Or.inl inside))
  have read : r.body.read.map (Subst.applyTerm σ) = r.body.read.map (Subst.applyTerm τ) :=
    List.map_congr_left fun t inside => agree t (mem_terms (Or.inr (Or.inl inside)))
  have tell : (r.body.tell.map fun pair => (Subst.applyTerm σ pair.1, Subst.applyTerm σ pair.2)) =
      r.body.tell.map fun pair => (Subst.applyTerm τ pair.1, Subst.applyTerm τ pair.2) := by
    refine List.map_congr_left fun e inside => ?_
    rw [agree e.1 (mem_terms (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨e, inside, rfl⟩))))),
      agree e.2 (mem_terms (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨e, inside, rfl⟩))))))]
  have checks : r.body.checks.map (Check.map (Subst.applyTerm σ)) =
      r.body.checks.map (Check.map (Subst.applyTerm τ)) := by
    refine List.map_congr_left fun check inside => ?_
    have term : ∀ u ∈ checkTerms check, Subst.applyTerm σ u = Subst.applyTerm τ u := fun u member =>
      agree u (mem_terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_flatMap.mpr ⟨check, inside, member⟩)))))))
    cases check with
    | equal left right =>
        show Check.equal (Subst.applyTerm σ left) (Subst.applyTerm σ right) =
          Check.equal (Subst.applyTerm τ left) (Subst.applyTerm τ right)
        rw [term left (by simp [checkTerms]), term right (by simp [checkTerms])]
    | predicate quantifier pattern =>
        show Check.predicate quantifier (Subst.applyTerm σ pattern) = Check.predicate quantifier (Subst.applyTerm τ pattern)
        rw [term pattern (by simp [checkTerms])]
    | count pattern number =>
        show Check.count (Subst.applyTerm σ pattern) number = Check.count (Subst.applyTerm τ pattern) number
        rw [term pattern (by simp [checkTerms])]
  have produce : r.body.produce.map (Subst.applyTerm σ) = r.body.produce.map (Subst.applyTerm τ) :=
    List.map_congr_left fun t inside =>
      agree t (mem_terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl inside)))))))
  show (⟨_, _, _, _, _⟩ : RuleInstance (Term atoms)) = ⟨_, _, _, _, _⟩
  rw [take, read, tell, checks, produce]

open Classical in
/-- **Re-opening a rule apart**: every unknown that is a term of the rule keeps its image under `ι`;
every other unknown `v` goes to `N + v`. -/
noncomputable def reopen (r : Rule Tm) (ι : Subst atoms) (N : ℕ) : Subst atoms :=
  fun v => if (Term.var v : Term atoms) ∈ r.terms then ι v else .var (N + v)

open Classical in
/-- The re-opening agrees with `ι` on the terms of the rule. -/
theorem reopen_of_term {r : Rule Tm} {ι : Subst atoms} {N : ℕ} {t : Term atoms} (inside : t ∈ r.terms) :
    Subst.applyTerm (reopen r ι N) t = Subst.applyTerm ι t := by
  cases t with
  | var v =>
      show (if (Term.var v : Term atoms) ∈ r.terms then ι v else .var (N + v)) = ι v
      rw [if_pos inside]
  | const _ => rfl
  | app fn _ => exact nomatch fn

open Classical in
/-- The re-opening sends every other unknown `v` to `N + v`. -/
theorem reopen_of_not_term {r : Rule Tm} {ι : Subst atoms} {N v : ℕ}
    (outside : (Term.var v : Term atoms) ∉ r.terms) : reopen r ι N v = .var (N + v) := by
  show (if (Term.var v : Term atoms) ∈ r.terms then ι v else .var (N + v)) = .var (N + v)
  rw [if_neg outside]

/-! ## Law 5 at one frame -/

/-- **Law 5 at one frame, without the terms hypothesis**: an equation guard that the rule's tells
entail may be dropped, whatever its terms, beside every program and at every state, for every barb
family. -/
theorem entailedGuard_congruent_oneFrame {B : Type*} {obs : B → State Tm ℕ → Prop} {r : Rule Tm}
    {l t : Tm r.locals}
    (entailed : X.Entails (a := r.locals) r.body.tell (fun b h =>
      X.E (a := b) (X.act (a := r.locals) (b := b) h l) (X.act (a := r.locals) (b := b) h t)))
    (Q : Program Tm) (s : State Tm ℕ) :
    Congruent X ℕ E obs ⟨Q ∪ {withGuard r l t}, s⟩ ⟨Q ∪ {r}, s⟩ := by
  -- Along any opening, the guard holds at every solution of the opened tells.
  have guard : ∀ σ ι : Subst atoms,
      X.Models (a := PUnit.unit) (b := PUnit.unit) σ
        (r.body.tell.map fun pair => (Subst.applyTerm ι pair.1, Subst.applyTerm ι pair.2)) →
      Subst.applyTerm σ (Subst.applyTerm ι l) = Subst.applyTerm σ (Subst.applyTerm ι t) := by
    intro σ ι told
    have solved : X.Models (a := r.locals) (b := PUnit.unit) (Subst.comp σ ι) r.body.tell := by
      intro e member
      have opened : Subst.applyTerm σ (Subst.applyTerm ι e.1) = Subst.applyTerm σ (Subst.applyTerm ι e.2) :=
        told _ (List.mem_map.mpr ⟨e, member, rfl⟩)
      show Subst.applyTerm (Subst.comp σ ι) e.1 = Subst.applyTerm (Subst.comp σ ι) e.2
      rw [Subst.applyTerm_comp, Subst.applyTerm_comp]
      exact opened
    have holds : Subst.applyTerm (Subst.comp σ ι) l = Subst.applyTerm (Subst.comp σ ι) t :=
      entailed PUnit.unit (Subst.comp σ ι) solved
    rwa [Subst.applyTerm_comp, Subst.applyTerm_comp] at holds
  -- A firing of the guarded rule is a firing of the rule, with the same result.
  have forward : Answers X ℕ E obs ({withGuard r l t} : Program Tm) {r} := by
    rintro s ⟨rule, member, ext, ι, selection, seen⟩ admitted
    have isRule : rule = withGuard r l t := member
    subst isRule
    refine ⟨⟨r, Set.mem_singleton _, ext, ι, selection, seen⟩, ?_, fun _ => Congruent.refl _⟩
    obtain ⟨fresh, shapes, enabled, solvable, checks, collect⟩ := (admits_iff _).mp admitted
    refine (admits_iff _).mpr ⟨fun b g h => ?_, shapes, enabled, solvable,
      fun check inside => checks check (List.mem_cons_of_mem _ inside), collect⟩
    obtain ⟨u, state, rule⟩ := fresh b g h
    exact ⟨u, state, fun v inside => rule v ((mem_withGuard_terms r l t v).mpr (Or.inl inside))⟩
  -- A firing of the rule is answered by the guarded rule re-opened apart, with the same result.
  have backward : Answers X ℕ E obs ({r} : Program Tm) {withGuard r l t} := by
    rintro s ⟨rule, member, ext, ι, selection, seen⟩ admitted
    have isRule : rule = r := member
    subst rule
    obtain ⟨fresh, shapes, enabled, solvable, checks, collect⟩ := (admits_iff _).mp admitted
    let N := bound (s.knowledge.map Prod.fst ++ s.knowledge.map Prod.snd ++
      s.present.toList.map s.label ++ r.terms.map (Subst.applyTerm ι))
    have mentionedBelow : ∀ u, s.Mentions u → above u ≤ N := by
      rintro u (inside | inside | ⟨o, present, rfl⟩)
      · exact above_le_bound (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ inside)))
      · exact above_le_bound (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ inside)))
      · exact above_le_bound (List.mem_append_left _ (List.mem_append_right _
          (List.mem_map_of_mem (Finset.mem_toList.mpr present))))
    have openedBelow : ∀ u ∈ r.terms, above (Subst.applyTerm ι u) ≤ N := fun u inside =>
      above_le_bound (List.mem_append_right _ (List.mem_map_of_mem inside))
    let ι' := reopen r ι N
    have onTerms : ∀ u ∈ r.terms, Subst.applyTerm ι' u = Subst.applyTerm ι u :=
      fun u inside => reopen_of_term inside
    have offTerms : ∀ w : ℕ, (Term.var w : Term atoms) ∉ r.terms → ι' w = .var (N + w) :=
      fun w outside => reopen_of_not_term outside
    obtain ⟨bodyEq, collectEq⟩ := map_congr_terms r onTerms
    let f : Firing ℕ E ({withGuard r l t} : Program Tm) s.frame :=
      ⟨withGuard r l t, Set.mem_singleton _, ext, ι', selection, seen⟩
    -- The information and the result depend on the opening only through the opened body.
    let row : ℕ → Term atoms := fun o =>
      X.act (a := s.frame) (b := E.target ext) (E.weaken ext) (s.label o)
    let info : RuleInstance (Term atoms) → EquationStore (Term atoms) := fun ρ =>
      X.applyStore (a := s.frame) (b := E.target ext) (E.weaken ext) s.knowledge ++
        ρ.take.zipWith (fun p o => (p, row o)) selection.taken ++
        ρ.read.zipWith (fun p o => (p, row o)) selection.read ++ ρ.tell
    let after : RuleInstance (Term atoms) → State Tm ℕ := fun ρ =>
      ⟨E.target ext, info ρ, fire s.present (selection.commit (T := Unit)),
        relabel (a := E.target ext) row selection.made ρ.produce⟩
    have infoEq : f.information X s =
        (⟨r, Set.mem_singleton r, ext, ι, selection, seen⟩ : Firing ℕ E ({r} : Program Tm)
          s.frame).information X s :=
      @congrArg _ _ (r.body.map (Subst.applyTerm ι')) (r.body.map (Subst.applyTerm ι)) info bodyEq
    have resultEq : f.result X s =
        (⟨r, Set.mem_singleton r, ext, ι, selection, seen⟩ : Firing ℕ E ({r} : Program Tm)
          s.frame).result X s :=
      @congrArg _ _ (r.body.map (Subst.applyTerm ι')) (r.body.map (Subst.applyTerm ι)) after bodyEq
    -- The re-opening is fresh for the guarded rule.
    have freshF : f.Fresh X s := by
      intro b g h
      obtain ⟨u, state, opened⟩ := fresh b g h
      let u' : Subst atoms := fun w => if N ≤ w then h (w - N) else u w
      have low : ∀ w, w < N → u' w = u w := fun w lt => if_neg (by omega)
      refine ⟨u', fun v mentioned => ?_, fun v inside => ?_⟩
      · have st : Subst.applyTerm u (Subst.applyTerm (Subst.id atoms) v) = Subst.applyTerm g v :=
          state v mentioned
        show Subst.applyTerm u' (Subst.applyTerm (Subst.id atoms) v) = Subst.applyTerm g v
        rw [Subst.applyTerm_id] at st ⊢
        rw [applyTerm_agree low (mentionedBelow v mentioned)]
        exact st
      · show Subst.applyTerm u' (Subst.applyTerm ι' v) = Subst.applyTerm h v
        by_cases term : v ∈ r.terms
        · have before : Subst.applyTerm u (Subst.applyTerm ι v) = Subst.applyTerm h v := opened v term
          rw [onTerms v term, applyTerm_agree low (openedBelow v term)]
          exact before
        · cases v with
          | var w =>
              show Subst.applyTerm u' (ι' w) = h w
              rw [offTerms w term]
              show (if N ≤ N + w then h (N + w - N) else u (N + w)) = h w
              rw [if_pos (Nat.le_add_right N w), Nat.add_sub_cancel_left]
          | const _ => rfl
          | app fn _ => exact nomatch fn
    refine ⟨f, (admits_iff f).mpr ⟨freshF, shapes, enabled, ?_, ?_, ?_⟩, fun _ => ?_⟩
    · rw [infoEq]
      exact solvable
    · intro check inside
      rcases List.mem_cons.mp inside with isGuard | old
      · subst isGuard
        intro b σ solved
        exact guard σ ι' fun e member => solved e (List.mem_append_right _ member)
      · have old' : check ∈ (r.body.map (Subst.applyTerm ι)).checks := by
          rw [← bodyEq]
          exact old
        rw [infoEq]
        exact checks check old'
    · intro q inside
      have inside' : q ∈ (r.collect.map (Subst.applyTerm ι)).zip seen := by
        rw [← collectEq]
        exact inside
      rw [infoEq]
      exact collect q inside'
    · rw [resultEq]
      exact Congruent.refl _
  have replaced := replace_congruent forward backward Q s
  rw [Set.union_comm, Set.union_comm ({r} : Program Tm)] at replaced
  exact replaced

/-- **An instance outside the hypothesis**: the guard `1 = 1` on `spawn` (make `5`) has a term that is
not a term of `spawn`, is entailed, and may be dropped. -/
theorem guard_outside_terms_example (Q : Program Tm) (s : State Tm ℕ) :
    c 1 ∉ spawn.terms ∧ Cong ⟨Q ∪ {withGuard spawn (c 1) (c 1)}, s⟩ ⟨Q ∪ {spawn}, s⟩ :=
  ⟨by simp [spawn, Rule.terms, c],
    entailedGuard_congruent_oneFrame (fun b _ _ => (X.equivalence b).refl _) Q s⟩

#print axioms above_le_bound
#print axioms applyTerm_agree
#print axioms mem_terms
#print axioms map_congr_terms
#print axioms reopen_of_term
#print axioms reopen_of_not_term
#print axioms entailedGuard_congruent_oneFrame
#print axioms guard_outside_terms_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtOneFrame

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtFirstOrder

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

/-- **First-order terms with the numbers as unknowns**: the given constants and function symbols with
their arities. -/
abbrev withUnknowns (C F : Type) (arity : F → ℕ) : LPSignature where
  constants := C
  vars := ℕ
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := F
  functionArity := arity

/-- **The flat signature of the examples is the case with no function symbols.** -/
theorem flat_instance : withUnknowns ℕ Empty Empty.elim = RuleSyntax.Controls.atoms := rfl

variable {C F : Type} {arity : F → ℕ}

local notation "Sig" => withUnknowns C F arity
local notation "Tm" => Terms (Term Sig)
local notation "X" => frames (FirstOrder.action Sig)
local notation "E" => ext (FirstOrder.action Sig)

/-! ## Unknowns below a bound -/

/-- One more than the largest unknown of a term (zero when it has none). -/
def above (t : Term Sig) : ℕ := t.freeVars.sup (· + 1)

theorem lt_above {t : Term Sig} {v : ℕ} (inside : v ∈ t.freeVars) : v < above t :=
  Nat.lt_of_succ_le (Finset.le_sup (f := (· + 1)) inside)

/-- A bound above the unknowns of every term of a list. -/
def bound (terms : List (Term Sig)) : ℕ := (terms.map above).sum

theorem above_le_bound {terms : List (Term Sig)} {t : Term Sig} (inside : t ∈ terms) :
    above t ≤ bound terms :=
  List.le_sum_of_mem (List.mem_map_of_mem inside)

/-- Substitutions that agree below a bound agree on every term whose unknowns lie below it. -/
theorem applyTerm_agree {σ τ : Subst Sig} {N : ℕ} (agree : ∀ v, v < N → σ v = τ v)
    {t : Term Sig} (below : above t ≤ N) : Subst.applyTerm σ t = Subst.applyTerm τ t :=
  Subst.applyTerm_congr fun v inside => agree v (lt_of_lt_of_le (lt_above inside) below)

/-- **Equal images determine the images of the unknowns**: first-order terms are free, so two
substitutions that send a term to the same term agree on its unknowns. -/
theorem agree_of_applyTerm_eq {σ τ : Subst Sig} :
    ∀ {t : Term Sig}, Subst.applyTerm σ t = Subst.applyTerm τ t → ∀ v ∈ t.freeVars, σ v = τ v
  | .var w, same, v, inside => by
      rw [(Term.mem_freeVars_var (σ := Sig)).mp inside]
      exact same
  | .const _, _, v, inside => by simp [Term.freeVars] at inside
  | .app f ts, same, v, inside => by
      obtain ⟨i, member⟩ := (Term.mem_freeVars_app (σ := Sig)).mp inside
      simp only [Subst.applyTerm_app] at same
      have children := congrFun (eq_of_heq (Term.app.inj same).2) i
      exact agree_of_applyTerm_eq children v member

/-! ## Re-opening a rule apart -/

/-- An unknown occurs in a term of the rule. -/
def RuleUnknown (r : Rule Tm) (v : ℕ) : Prop := ∃ t ∈ r.terms, v ∈ t.freeVars

/-- Every term of a rule, by where it occurs. -/
theorem mem_terms {r : Rule Tm} {t : Term Sig}
    (inside : t ∈ r.body.take ∨ t ∈ r.body.read ∨ t ∈ r.body.tell.map Prod.fst ∨
      t ∈ r.body.tell.map Prod.snd ∨ t ∈ r.body.checks.flatMap checkTerms ∨ t ∈ r.body.produce ∨
      t ∈ r.collect) : t ∈ r.terms := by
  unfold Rule.terms
  simp only [List.mem_append]
  tauto

/-- **Substitutions that agree on the terms of a rule open it alike**: its body and its collect query. -/
theorem map_congr_terms (r : Rule Tm) {σ τ : Subst Sig}
    (agree : ∀ t ∈ r.terms, Subst.applyTerm σ t = Subst.applyTerm τ t) :
    r.body.map (Subst.applyTerm σ) = r.body.map (Subst.applyTerm τ) ∧
      r.collect.map (Subst.applyTerm σ) = r.collect.map (Subst.applyTerm τ) := by
  have collect : r.collect.map (Subst.applyTerm σ) = r.collect.map (Subst.applyTerm τ) :=
    List.map_congr_left fun t inside =>
      agree t (mem_terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr inside)))))))
  refine ⟨?_, collect⟩
  have take : r.body.take.map (Subst.applyTerm σ) = r.body.take.map (Subst.applyTerm τ) :=
    List.map_congr_left fun t inside => agree t (mem_terms (Or.inl inside))
  have read : r.body.read.map (Subst.applyTerm σ) = r.body.read.map (Subst.applyTerm τ) :=
    List.map_congr_left fun t inside => agree t (mem_terms (Or.inr (Or.inl inside)))
  have tell : (r.body.tell.map fun pair => (Subst.applyTerm σ pair.1, Subst.applyTerm σ pair.2)) =
      r.body.tell.map fun pair => (Subst.applyTerm τ pair.1, Subst.applyTerm τ pair.2) := by
    refine List.map_congr_left fun e inside => ?_
    rw [agree e.1 (mem_terms (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨e, inside, rfl⟩))))),
      agree e.2 (mem_terms (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨e, inside, rfl⟩))))))]
  have checks : r.body.checks.map (Check.map (Subst.applyTerm σ)) =
      r.body.checks.map (Check.map (Subst.applyTerm τ)) := by
    refine List.map_congr_left fun check inside => ?_
    have term : ∀ u ∈ checkTerms check, Subst.applyTerm σ u = Subst.applyTerm τ u := fun u member =>
      agree u (mem_terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_flatMap.mpr ⟨check, inside, member⟩)))))))
    cases check with
    | equal left right =>
        show Check.equal (Subst.applyTerm σ left) (Subst.applyTerm σ right) =
          Check.equal (Subst.applyTerm τ left) (Subst.applyTerm τ right)
        rw [term left (by simp [checkTerms]), term right (by simp [checkTerms])]
    | predicate quantifier pattern =>
        show Check.predicate quantifier (Subst.applyTerm σ pattern) = Check.predicate quantifier (Subst.applyTerm τ pattern)
        rw [term pattern (by simp [checkTerms])]
    | count pattern number =>
        show Check.count (Subst.applyTerm σ pattern) number = Check.count (Subst.applyTerm τ pattern) number
        rw [term pattern (by simp [checkTerms])]
  have produce : r.body.produce.map (Subst.applyTerm σ) = r.body.produce.map (Subst.applyTerm τ) :=
    List.map_congr_left fun t inside =>
      agree t (mem_terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl inside)))))))
  show (⟨_, _, _, _, _⟩ : RuleInstance (Term Sig)) = ⟨_, _, _, _, _⟩
  rw [take, read, tell, checks, produce]

open Classical in
/-- **Re-opening a rule apart**: every unknown that occurs in a term of the rule keeps its image
under `ι`; every other unknown `v` goes to `N + v`. -/
noncomputable def reopen (r : Rule Tm) (ι : Subst Sig) (N : ℕ) : Subst Sig :=
  fun v => if RuleUnknown r v then ι v else .var (N + v)

theorem reopen_of_unknown {r : Rule Tm} {ι : Subst Sig} {N v : ℕ} (inside : RuleUnknown r v) :
    reopen r ι N v = ι v := by
  classical
  exact if_pos inside

theorem reopen_of_not_unknown {r : Rule Tm} {ι : Subst Sig} {N v : ℕ} (outside : ¬ RuleUnknown r v) :
    reopen r ι N v = .var (N + v) := by
  classical
  exact if_neg outside

/-- The re-opening agrees with `ι` on the terms of the rule. -/
theorem reopen_of_term {r : Rule Tm} {ι : Subst Sig} {N : ℕ} {t : Term Sig} (inside : t ∈ r.terms) :
    Subst.applyTerm (reopen r ι N) t = Subst.applyTerm ι t :=
  Subst.applyTerm_congr fun _ member => reopen_of_unknown ⟨t, inside, member⟩

/-! ## Law 5 at first-order terms with function symbols -/

/-- **Law 5 at one frame over first-order terms with the numbers as unknowns, with function symbols,
without the terms hypothesis**: an equation guard that the rule's tells entail may be dropped, whatever
its terms, beside every program and at every state, for every barb family. Every unknown of the guard
either occurs in a term of the rule, and then freshness of the rule's opening already realizes it
(first-order terms are free: `agree_of_applyTerm_eq`), or it does not, and then it is opened above
everything the state and the old opening mention. -/
theorem entailedGuard_congruent_firstOrder {B : Type*} {obs : B → State Tm ℕ → Prop} {r : Rule Tm}
    {l t : Term Sig}
    (entailed : (X).Entails (a := r.locals) r.body.tell (fun b h =>
      (X).E (a := b) ((X).act (a := r.locals) (b := b) h l) ((X).act (a := r.locals) (b := b) h t)))
    (Q : Program Tm) (s : State Tm ℕ) :
    Congruent X ℕ E obs ⟨Q ∪ {withGuard r l t}, s⟩ ⟨Q ∪ {r}, s⟩ := by
  -- Along any opening, the guard holds at every solution of the opened tells.
  have guard : ∀ σ ι : Subst Sig,
      (X).Models (a := PUnit.unit) (b := PUnit.unit) σ
        (r.body.tell.map fun pair => (Subst.applyTerm ι pair.1, Subst.applyTerm ι pair.2)) →
      Subst.applyTerm σ (Subst.applyTerm ι l) = Subst.applyTerm σ (Subst.applyTerm ι t) := by
    intro σ ι told
    have solved : (X).Models (a := r.locals) (b := PUnit.unit) (Subst.comp σ ι) r.body.tell := by
      intro e member
      have opened : Subst.applyTerm σ (Subst.applyTerm ι e.1) = Subst.applyTerm σ (Subst.applyTerm ι e.2) :=
        told _ (List.mem_map.mpr ⟨e, member, rfl⟩)
      show Subst.applyTerm (Subst.comp σ ι) e.1 = Subst.applyTerm (Subst.comp σ ι) e.2
      rw [Subst.applyTerm_comp, Subst.applyTerm_comp]
      exact opened
    have holds : Subst.applyTerm (Subst.comp σ ι) l = Subst.applyTerm (Subst.comp σ ι) t :=
      entailed PUnit.unit (Subst.comp σ ι) solved
    rwa [Subst.applyTerm_comp, Subst.applyTerm_comp] at holds
  -- A firing of the guarded rule is a firing of the rule, with the same result.
  have forward : Answers X ℕ E obs ({withGuard r l t} : Program Tm) {r} := by
    rintro s ⟨rule, member, ext, ι, selection, seen⟩ admitted
    have isRule : rule = withGuard r l t := member
    subst isRule
    refine ⟨⟨r, Set.mem_singleton _, ext, ι, selection, seen⟩, ?_, fun _ => Congruent.refl _⟩
    obtain ⟨fresh, shapes, enabled, solvable, checks, collect⟩ := (admits_iff _).mp admitted
    refine (admits_iff _).mpr ⟨fun b g h => ?_, shapes, enabled, solvable,
      fun check inside => checks check (List.mem_cons_of_mem _ inside), collect⟩
    obtain ⟨u, state, rule⟩ := fresh b g h
    exact ⟨u, state, fun v inside => rule v ((mem_withGuard_terms r l t v).mpr (Or.inl inside))⟩
  -- A firing of the rule is answered by the guarded rule re-opened apart, with the same result.
  have backward : Answers X ℕ E obs ({r} : Program Tm) {withGuard r l t} := by
    rintro s ⟨rule, member, ext, ι, selection, seen⟩ admitted
    have isRule : rule = r := member
    subst rule
    obtain ⟨fresh, shapes, enabled, solvable, checks, collect⟩ := (admits_iff _).mp admitted
    let N := bound (s.knowledge.map Prod.fst ++ s.knowledge.map Prod.snd ++
      s.present.toList.map s.label ++ r.terms.map (Subst.applyTerm ι))
    have mentionedBelow : ∀ u, s.Mentions u → above u ≤ N := by
      rintro u (inside | inside | ⟨o, present, rfl⟩)
      · exact above_le_bound (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ inside)))
      · exact above_le_bound (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ inside)))
      · exact above_le_bound (List.mem_append_left _ (List.mem_append_right _
          (List.mem_map_of_mem (Finset.mem_toList.mpr present))))
    have openedBelow : ∀ u ∈ r.terms, above (Subst.applyTerm ι u) ≤ N := fun u inside =>
      above_le_bound (List.mem_append_right _ (List.mem_map_of_mem inside))
    let ι' := reopen r ι N
    have onTerms : ∀ u ∈ r.terms, Subst.applyTerm ι' u = Subst.applyTerm ι u :=
      fun u inside => reopen_of_term inside
    obtain ⟨bodyEq, collectEq⟩ := map_congr_terms r onTerms
    let f : Firing ℕ E ({withGuard r l t} : Program Tm) s.frame :=
      ⟨withGuard r l t, Set.mem_singleton _, ext, ι', selection, seen⟩
    -- The information and the result depend on the opening only through the opened body.
    let row : ℕ → Term Sig := fun o =>
      (X).act (a := s.frame) (b := (E).target ext) ((E).weaken ext) (s.label o)
    let info : RuleInstance (Term Sig) → EquationStore (Term Sig) := fun ρ =>
      (X).applyStore (a := s.frame) (b := (E).target ext) ((E).weaken ext) s.knowledge ++
        ρ.take.zipWith (fun p o => (p, row o)) selection.taken ++
        ρ.read.zipWith (fun p o => (p, row o)) selection.read ++ ρ.tell
    let after : RuleInstance (Term Sig) → State Tm ℕ := fun ρ =>
      ⟨(E).target ext, info ρ, fire s.present (selection.commit (T := Unit)),
        relabel (a := (E).target ext) row selection.made ρ.produce⟩
    have infoEq : f.information X s =
        (⟨r, Set.mem_singleton r, ext, ι, selection, seen⟩ : Firing ℕ E ({r} : Program Tm)
          s.frame).information X s :=
      @congrArg _ _ (r.body.map (Subst.applyTerm ι')) (r.body.map (Subst.applyTerm ι)) info bodyEq
    have resultEq : f.result X s =
        (⟨r, Set.mem_singleton r, ext, ι, selection, seen⟩ : Firing ℕ E ({r} : Program Tm)
          s.frame).result X s :=
      @congrArg _ _ (r.body.map (Subst.applyTerm ι')) (r.body.map (Subst.applyTerm ι)) after bodyEq
    -- The re-opening is fresh for the guarded rule.
    have freshF : f.Fresh X s := by
      intro b g h
      obtain ⟨u, state, opened⟩ := fresh b g h
      let u' : Subst Sig := fun w => if N ≤ w then h (w - N) else u w
      have low : ∀ w, w < N → u' w = u w := fun w lt => if_neg (by omega)
      -- the old opening, followed by `u`, agrees with `h` on every unknown of the rule
      have onUnknowns : ∀ v, RuleUnknown r v → Subst.applyTerm u (ι v) = h v := by
        rintro v ⟨w, inside, member⟩
        have both : Subst.applyTerm (Subst.comp u ι) w = Subst.applyTerm h w := by
          rw [Subst.applyTerm_comp]
          exact opened w inside
        exact agree_of_applyTerm_eq both v member
      have imageBelow : ∀ v, RuleUnknown r v → above (ι v) ≤ N := by
        rintro v ⟨w, inside, member⟩
        refine le_trans ?_ (openedBelow w inside)
        refine Finset.sup_le fun x inImage => ?_
        have inOpened : x ∈ (Subst.applyTerm ι w).freeVars :=
          Subst.mem_freeVars_applyTerm (σ := Sig) |>.mpr ⟨v, member, inImage⟩
        exact Finset.le_sup (f := (· + 1)) inOpened
      refine ⟨u', fun v mentioned => ?_, fun v inside => ?_⟩
      · have st : Subst.applyTerm u (Subst.applyTerm (Subst.id Sig) v) = Subst.applyTerm g v :=
          state v mentioned
        show Subst.applyTerm u' (Subst.applyTerm (Subst.id Sig) v) = Subst.applyTerm g v
        rw [Subst.applyTerm_id] at st ⊢
        rw [applyTerm_agree low (mentionedBelow v mentioned)]
        exact st
      · show Subst.applyTerm u' (Subst.applyTerm ι' v) = Subst.applyTerm h v
        rw [← Subst.applyTerm_comp]
        refine Subst.applyTerm_congr fun w member => ?_
        show Subst.applyTerm u' (reopen r ι N w) = h w
        by_cases known : RuleUnknown r w
        · rw [reopen_of_unknown known, applyTerm_agree low (imageBelow w known)]
          exact onUnknowns w known
        · rw [reopen_of_not_unknown known]
          show (if N ≤ N + w then h (N + w - N) else u (N + w)) = h w
          rw [if_pos (Nat.le_add_right N w), Nat.add_sub_cancel_left]
    refine ⟨f, (admits_iff f).mpr ⟨freshF, shapes, enabled, ?_, ?_, ?_⟩, fun _ => ?_⟩
    · rw [infoEq]
      exact solvable
    · intro check inside
      rcases List.mem_cons.mp inside with isGuard | old
      · subst isGuard
        intro b σ solved
        exact guard σ ι' fun e member => solved e (List.mem_append_right _ member)
      · have old' : check ∈ (r.body.map (Subst.applyTerm ι)).checks := by
          rw [← bodyEq]
          exact old
        rw [infoEq]
        exact checks check old'
    · intro q inside
      have inside' : q ∈ (r.collect.map (Subst.applyTerm ι)).zip seen := by
        rw [← collectEq]
        exact inside
      rw [infoEq]
      exact collect q inside'
    · rw [resultEq]
      exact Congruent.refl _
  have replaced := replace_congruent forward backward Q s
  rw [Set.union_comm, Set.union_comm ({r} : Program Tm)] at replaced
  exact replaced

/-! ## An instance with a function symbol and a new unknown -/

/-- Terms with one binary function symbol, `pair`, and the numbers as constants and unknowns. -/
abbrev pairs : LPSignature := withUnknowns ℕ Unit (fun _ => 2)

/-- `pair a b`. -/
def pair (a b : Term pairs) : Term pairs := .app () ![a, b]

/-- The unknown `n`. -/
def unknown (n : ℕ) : Term pairs := .var n

/-- **Read `pair x y`, tell `x = y`, make `y`.** -/
def joinRule : Rule (Terms (Term pairs)) :=
  ⟨PUnit.unit, ⟨[], [pair (unknown 0) (unknown 1)], [(unknown 0, unknown 1)], [], [unknown 1]⟩, []⟩

/-- **The guard `pair x z = pair y z` may be dropped**: the tell `x = y` entails it, its terms are not
terms of the rule, and `z` is an unknown the rule does not have. -/
theorem pair_guard_example (Q : Program (Terms (Term pairs))) (s : State (Terms (Term pairs)) ℕ) :
    pair (unknown 0) (unknown 2) ∉ joinRule.terms ∧ pair (unknown 1) (unknown 2) ∉ joinRule.terms ∧
      ¬ RuleUnknown joinRule 2 ∧
      Congruent (frames (FirstOrder.action pairs)) ℕ (ext (FirstOrder.action pairs))
        (MayBarb (frames (FirstOrder.action pairs)))
        ⟨Q ∪ {withGuard joinRule (pair (unknown 0) (unknown 2)) (pair (unknown 1) (unknown 2))}, s⟩
        ⟨Q ∪ {joinRule}, s⟩ := by
  refine ⟨?_, ?_, ?_, entailedGuard_congruent_firstOrder ?_ Q s⟩
  · simp [joinRule, Rule.terms, pair, unknown]
  · simp [joinRule, Rule.terms, pair, unknown]
  · rintro ⟨t, inside, member⟩
    simp only [joinRule, Rule.terms, List.map_nil, List.flatMap_nil, List.nil_append, List.append_nil,
      List.mem_cons, List.map_cons, List.cons_append, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl <;>
      simp [pair, unknown, Term.freeVars] at member
  · intro b h told
    have same : h 0 = h 1 := told (unknown 0, unknown 1) (List.mem_singleton_self _)
    show Subst.applyTerm h (pair (unknown 0) (unknown 2)) = Subst.applyTerm h (pair (unknown 1) (unknown 2))
    simp only [pair, Subst.applyTerm_app]
    congr 1
    funext i
    fin_cases i
    · simpa [unknown] using same
    · rfl

#print axioms agree_of_applyTerm_eq
#print axioms reopen_of_term
#print axioms entailedGuard_congruent_firstOrder
#print axioms flat_instance
#print axioms pair_guard_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtFirstOrder

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtOneUnknown

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

/-- **Terms with one unknown**: numerals as constants, one variable, no function symbols. -/
abbrev oneUnknown : LPSignature where
  constants := ℕ
  vars := Unit
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Empty
  functionArity := Empty.elim

/-- The first-order action on these terms. -/
abbrev action : SubstitutionAction (Term oneUnknown) (Subst oneUnknown) := FirstOrder.action oneUnknown

/-- Terms at the one frame. -/
abbrev Tm := Terms (Term oneUnknown)

/-- The frame action. -/
abbrev X := frames action

/-- The identity extension. -/
abbrev E := ext action

/-- The unknown. -/
def v : Term oneUnknown := .var ()

/-- The constant `n`. -/
def k (n : ℕ) : Term oneUnknown := .const n

/-- Make `5`. -/
def make : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [], [k 5]⟩, []⟩

/-- One row, labelled by the unknown. -/
def rowV : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => v⟩

/-- **The rule without the guard fires at the row `v`.** -/
theorem make_moves : ∃ T, Reduces X ℕ E ⟨∅ ∪ {make}, rowV⟩ T := by
  let f : Firing ℕ E (∅ ∪ {make}) rowV.frame :=
    ⟨make, Or.inr (Set.mem_singleton _), PUnit.unit, Subst.id oneUnknown, ⟨[], [], [1]⟩, []⟩
  have admitted : f.Admits X rowV := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_,
      ⟨PUnit.unit, Subst.id oneUnknown, fun e inside => absurd inside List.not_mem_nil⟩,
      fun check inside => absurd inside List.not_mem_nil, fun q inside => absurd inside List.not_mem_nil⟩
    · apply RuleSyntax.Examples.fresh_of_ground action rowV f
      intro t member σ
      simp only [f, make, Rule.terms, List.map_nil, List.flatMap_nil, List.nil_append, List.append_nil,
        List.mem_singleton] at member
      subst member
      rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit, rowV]
      · intro q inside
        simp [f, Selection.commit] at inside
  exact ⟨_, reduces_of_admits f admitted⟩

/-- **The guarded rule fires at no state that mentions the unknown**: its opening would have to send
the guard's unknown apart from the unknown the state mentions, and there is no other. -/
theorem guarded_stuck : ¬ ∃ T, Reduces X ℕ E ⟨∅ ∪ {withGuard make v v}, rowV⟩ T := by
  rintro ⟨T, -, ⟨rule, member, ext, ι, selection, seen⟩, admitted, -⟩
  rcases (Set.mem_union _ _ _).mp member with none | isRule
  · exact Set.notMem_empty _ none
  have same : rule = withGuard make v v := isRule
  subst same
  obtain ⟨fresh, -⟩ := (admits_iff _).mp admitted
  have term : v ∈ (withGuard make v v).terms := by simp [Rule.terms, checkTerms]
  obtain ⟨u, state, opened⟩ := fresh PUnit.unit (fun _ => k 0) (fun _ => k 1)
  obtain ⟨u', -, opened'⟩ := fresh PUnit.unit (fun _ => k 0) (fun _ => k 2)
  have seen : u () = k 0 := state v (Or.inr (Or.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩))
  have one : Subst.applyTerm u (ι ()) = k 1 := opened v term
  have two : Subst.applyTerm u' (ι ()) = k 2 := opened' v term
  cases h : ι () with
  | var w =>
      rw [h] at one
      have bad : (k 0 : Term oneUnknown) = k 1 := seen.symm.trans one
      exact absurd (Term.const.inj bad) (by decide)
  | const n =>
      rw [h] at one two
      have bad : (1 : ℕ) = 2 := (Term.const.inj one).symm.trans (Term.const.inj two)
      exact absurd bad (by decide)
  | app f _ => exact nomatch f

/-- **At one frame with one unknown, Law 5 fails without its terms hypothesis**: the guard `v = v` is
entailed by the tells of `make` and its term is not a term of `make`, and the rule with and without the
guard are not congruent at the row `v`. Of the law's hypotheses the control fails exactly the terms
hypothesis, at a frame that has no unknown apart from what the state mentions: what it shows needed is a
supply of fresh unknowns (`not_fresh_of_mentioned`, `fresh_supply_needed`). With that supply, at
first-order frames with the numbers as unknowns, the terms hypothesis is not needed
(`AtFirstOrder.entailedGuard_congruent_firstOrder`). -/
theorem guard_terms_needed :
    X.Entails (a := PUnit.unit) make.body.tell
        (fun b h => X.E (a := b) (X.act (a := PUnit.unit) (b := b) h v)
          (X.act (a := PUnit.unit) (b := b) h v)) ∧
      v ∉ make.terms ∧
      ¬ Congruent X ℕ E (MayBarb X) ⟨∅ ∪ {withGuard make v v}, rowV⟩ ⟨∅ ∪ {make}, rowV⟩ :=
  ⟨fun b _ _ => (X.equivalence b).refl _, by simp [make, Rule.terms, v, k],
    fun related => guarded_stuck (related.symm.moves make_moves)⟩

/-! ## What the frame with one unknown lacks: a supply of fresh unknowns -/

/-- **No fresh opening where the one unknown is mentioned**: a rule with the unknown among its terms
has no fresh opening at any state that mentions it, guard or no guard. -/
theorem not_fresh_of_mentioned {P : Program Tm} {s : State Tm ℕ} (f : Firing ℕ E P s.frame)
    (term : v ∈ f.rule.terms) (mentioned : s.Mentions v) : ¬ f.Fresh X s := by
  intro fresh
  obtain ⟨u, state, opened⟩ := fresh PUnit.unit (fun _ => k 0) (fun _ => k 1)
  obtain ⟨u', -, opened'⟩ := fresh PUnit.unit (fun _ => k 0) (fun _ => k 2)
  have seen : u () = k 0 := state v mentioned
  have one : Subst.applyTerm u (f.opening ()) = k 1 := opened v term
  have two : Subst.applyTerm u' (f.opening ()) = k 2 := opened' v term
  cases h : f.opening () with
  | var w =>
      rw [h] at one
      have bad : (k 0 : Term oneUnknown) = k 1 := seen.symm.trans one
      exact absurd (Term.const.inj bad) (by decide)
  | const n =>
      rw [h] at one two
      have bad : (1 : ℕ) = 2 := (Term.const.inj one).symm.trans (Term.const.inj two)
      exact absurd bad (by decide)
  | app fn _ => exact nomatch fn

/-- Read any row, make `5`: a rule with no check. -/
def readAny : Rule Tm := ⟨PUnit.unit, ⟨[], [v], [], [], [k 5]⟩, []⟩

theorem readAny_term : v ∈ readAny.terms := by simp [readAny, Rule.terms]

/-- **At the row `v`, reading any row does not move**: no guard is involved. -/
theorem readAny_stuck : ¬ ∃ T, Reduces X ℕ E ⟨∅ ∪ {readAny}, rowV⟩ T := by
  rintro ⟨T, -, ⟨rule, member, ext, ι, selection, seen⟩, admitted, -⟩
  rcases (Set.mem_union _ _ _).mp member with none | isRule
  · exact Set.notMem_empty _ none
  have same : rule = readAny := isRule
  subst same
  obtain ⟨fresh, -⟩ := (admits_iff _).mp admitted
  exact not_fresh_of_mentioned _ readAny_term
    (Or.inr (Or.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩)) fresh

/-- One row `7`. -/
def rowSeven : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => k 7⟩

/-- **At the row `7`, reading any row moves.** -/
theorem readAny_moves_ground : ∃ T, Reduces X ℕ E ⟨∅ ∪ {readAny}, rowSeven⟩ T := by
  let f : Firing ℕ E (∅ ∪ {readAny}) rowSeven.frame :=
    ⟨readAny, Or.inr (Set.mem_singleton _), PUnit.unit, Subst.id oneUnknown, ⟨[], [0], [1]⟩, []⟩
  have info : f.information X rowSeven = [(v, k 7)] := rfl
  have admitted : f.Admits X rowSeven := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩,
      by decide, ⟨PUnit.unit, fun _ => k 7, ?_⟩, fun check inside => absurd inside List.not_mem_nil,
      fun q inside => absurd inside List.not_mem_nil⟩
    · intro b g h
      refine ⟨h, fun t mentioned => ?_, fun t _ => ?_⟩
      · rcases mentioned with none | none | ⟨o, -, rfl⟩
        · exact absurd none List.not_mem_nil
        · exact absurd none List.not_mem_nil
        · rfl
      · show Subst.applyTerm h (Subst.applyTerm (Subst.id oneUnknown) t) = Subst.applyTerm h t
        rw [Subst.applyTerm_id]
    · intro e inside
      rw [info, List.mem_singleton] at inside
      subst inside
      rfl
  exact ⟨_, reduces_of_admits f admitted⟩

/-- **What the frame with one unknown lacks is a supply of fresh unknowns, not the terms of a guard**:
every rule that has the unknown among its terms is stuck at every state that mentions it; the rule
that reads any row and makes `5`, which has no check at all, does not move at the row `v` and moves at
the row `7`. -/
theorem fresh_supply_needed :
    (∀ {P : Program Tm} {s : State Tm ℕ} (f : Firing ℕ E P s.frame), v ∈ f.rule.terms →
      s.Mentions v → ¬ f.Fresh X s) ∧
      readAny.body.checks = [] ∧ (¬ ∃ T, Reduces X ℕ E ⟨∅ ∪ {readAny}, rowV⟩ T) ∧
      ∃ T, Reduces X ℕ E ⟨∅ ∪ {readAny}, rowSeven⟩ T :=
  ⟨fun f term mentioned => not_fresh_of_mentioned f term mentioned, rfl, readAny_stuck,
    readAny_moves_ground⟩

#print axioms make_moves
#print axioms guarded_stuck
#print axioms guard_terms_needed
#print axioms not_fresh_of_mentioned
#print axioms readAny_stuck
#print axioms readAny_moves_ground
#print axioms fresh_supply_needed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtOneUnknown
