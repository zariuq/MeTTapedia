import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Branching

/-!
# A recursively enumerable step relation is hosted in the may sense: guess, check, commit

A transition system on the naturals whose step relation `R` is recursively enumerable, in Mathlib's usual sense
(`REPred`: the domain of a partial recursive function), is the system of a code that checks a guess
(`exists_check`): it evaluates `[n, y]` to `[y]` when `R n y` and has no value otherwise (`Checks`).

## The program (`guessRules ec`)

A term-rewriting machine (`Machines.TermRewriting`): the nineteen schemas of the machine and three more, over
one new row, the guessing row `guessRow x y` (from `x`, the guess `y`):

* `guessUp`: the guess grows by one;
* `guessStop ec`: the guess is checked: the pending evaluation of the code on `[x, y]`;
* `restartGuess`: a halted row with one output `[y]` starts guessing from `y`.

Every rule takes one row and makes one row. The program guesses: a guess may be wrong, and then its check never
reaches a halted row (`wrong_guess_never_commits`), and it may guess for ever (`guess_forever`).

## The may sense

* `rootMay`: a `Hosting.MayHosting` at the level of rows: every rewrite is read back as no step or one (the step
  to `y` when the check of `y` halts), the state `guessRow n 0` represents `n` and nothing related to another
  number, and every step `n → m` is realized from the guessing row of `n` to the guessing row of `m`.
* `stepMay`: the same on the one-match step, composed with `rootCorrespondence`.
* **`hosts_re`**: every recursively enumerable step relation is hosted in the may sense by a finite program:
  `n` reaches `m` exactly when the program, run from the state of `guessRow n 0`, reaches a state that reads as
  `guessRow m 0`.

## Control: infinitely many successors

The system `fromZero` (`0` steps to every number) is recursively enumerable, even decidable (`fromZero_re`), so it
is hosted in the may sense (`fromZero_may`). No weak correspondence to the step of any finite list of
range-restricted positive rules, with an observation read off the bag, relates `0` to a state that reads as a
bag (`fromZero_not_weak`): the weak sense forces finitely many successors (`Hosting.successors_finite_of_program`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Enumerable

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec
open NamesOnTheStep (Expr)
open Presentation.Schematic
open PartialRecursive
open Branching (spineHead row_head rootStep_head eval_iff_runFor sucP schemas_closed)
open Representation.Hosting (MayHosting WeakCorrespondence successors_finite_of_program)

/-! ## A code that checks a guess -/

/-- **A code checks guesses for a relation**: it evaluates `[n, y]` to `[y]` when `R n y`, and has no value
otherwise. -/
def Checks (R : ℕ → ℕ → Prop) (ec : Code) : Prop :=
  ∀ (n y : ℕ) (w : List ℕ), w ∈ ec.eval [n, y] ↔ R n y ∧ w = [y]

/-- **A recursively enumerable relation has a code that checks guesses for it.** -/
theorem exists_check {R : ℕ → ℕ → Prop} (re : REPred fun p : ℕ × ℕ => R p.1 p.2) : ∃ ec, Checks R ec := by
  have output : Computable₂ fun (p : ℕ × ℕ) (_ : Unit) => p.2 := (Computable.snd.comp Computable.fst).to₂
  have mapped : Partrec fun p : ℕ × ℕ => (Part.assert (R p.1 p.2) fun _ => Part.some ()).map fun _ => p.2 :=
    Partrec.map re output
  have twoArgs := (Nat.Partrec'.part_iff₂
    (f := fun n y => (Part.assert (R n y) fun _ => Part.some ()).map fun _ => y)).mpr mapped
  obtain ⟨ec, evaluates⟩ := Code.exists_code twoArgs
  refine ⟨ec, fun n y w => ?_⟩
  have evaluated : ec.eval [n, y] = pure <$> ((Part.assert (R n y) fun _ => Part.some ()).map fun _ => y) :=
    evaluates ⟨[n, y], rfl⟩
  rw [evaluated]
  constructor
  · intro member
    obtain ⟨a, inside, rfl⟩ := (Part.mem_map_iff _).mp member
    obtain ⟨u, asserted, rfl⟩ := (Part.mem_map_iff _).mp inside
    obtain ⟨holds, -⟩ := Part.mem_assert_iff.mp asserted
    exact ⟨holds, rfl⟩
  · rintro ⟨holds, rfl⟩
    exact (Part.mem_map_iff _).mpr ⟨y, (Part.mem_map_iff _).mpr
      ⟨(), Part.mem_assert_iff.mpr ⟨holds, Part.mem_some ()⟩, rfl⟩, rfl⟩

/-! ## The program -/

/-- **A guessing row**: from `x`, the guess `y`. -/
def guessRow (x y : ℕ) : Expr := .app (.app (.sym 23) (eNat x)) (eNat y)

/-- A guessing row, as a pattern. -/
def guessP (x y : Tm) : Tm := ap (ap (con 23) x) y

/-- The guess grows by one. -/
def guessUp : Tm × Tm := (guessP (unk 0) (unk 1), guessP (unk 0) (sucP (unk 1)))

/-- The guess is checked: the pending evaluation of the code on `[x, y]`. -/
def guessStop (ec : Code) : Tm × Tm :=
  (guessP (unk 0) (unk 1), normalP (toTerm (eCode ec)) (con 11) (consP (unk 0) (consP (unk 1) (con 2))))

/-- A halted row with one output `[y]` starts guessing from `y`. -/
def restartGuess : Tm × Tm := (restartLhs, guessP (unk 0) (con 0))

/-- **The schemas of the program**: the machine's, and the three of guessing. -/
def guessSchemas (ec : Code) : List (Tm × Tm) := schemas ++ [guessUp, guessStop ec, restartGuess]

/-- **The program**: one rule per schema, each taking one row and making one row. -/
def guessRules (ec : Code) : List SRule := rootRules (guessSchemas ec)

theorem guessSchemas_closed (ec : Code) : ∀ p ∈ guessSchemas ec, ∀ x ∈ unknowns p.2, x ∈ unknowns p.1 := by
  intro p member x inside
  rcases List.mem_append.mp member with machine | control
  · exact schemas_closed p machine x inside
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at control
    rcases control with rfl | rfl | rfl
    · revert x
      decide
    · have unfolded : x ∈ ((([] ++ unknowns (toTerm (eCode ec))) ++ []) ++
          (([] ++ [0]) ++ (([] ++ [1]) ++ []))) := inside
      rw [unknowns_toTerm] at unfolded
      have cases : x = 0 ∨ x = 1 := by simpa using unfolded
      show x ∈ unknowns (guessP (unk 0) (unk 1))
      rcases cases with rfl | rfl <;> decide
    · revert x
      decide

theorem guess_fragment (ec : Code) : ∀ r ∈ guessRules ec, RangeRestrictedPositive r :=
  rootRules_fragment (guessSchemas_closed ec)

theorem mem_guessUp (ec : Code) : guessUp ∈ guessSchemas ec :=
  List.mem_append_right _ List.mem_cons_self

theorem mem_guessStop (ec : Code) : guessStop ec ∈ guessSchemas ec :=
  List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem mem_restartGuess (ec : Code) : restartGuess ∈ guessSchemas ec :=
  List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-! ## The root rewrites -/

/-- **At a guessing row**: the guess grows, or it is checked. -/
theorem rootStep_guessRow {ec : Code} {x y : ℕ} {e' : Expr} (rooted : RootStep (guessSchemas ec) (guessRow x y) e') :
    e' = guessRow x (y + 1) ∨ e' = (Point.normal ec .halt [x, y]).row := by
  obtain ⟨pair, member, θ, matched, rfl⟩ := rooted
  rcases List.mem_append.mp member with machine | control
  · rcases rootStep_head ⟨pair, machine, θ, matched, rfl⟩ with h | h <;> cases h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at control
    rcases control with rfl | rfl | rfl
    · have parts := Expr.app.inj matched
      have first : θ 0 = eNat x := (Expr.app.inj parts.1).2
      have second : θ 1 = eNat y := parts.2
      left
      show Expr.app (Expr.app (Expr.sym 23) (θ 0)) (Expr.app (Expr.sym 1) (θ 1)) = guessRow x (y + 1)
      rw [first, second]
      rfl
    · have parts := Expr.app.inj matched
      have first : θ 0 = eNat x := (Expr.app.inj parts.1).2
      have second : θ 1 = eNat y := parts.2
      right
      show Expr.app (Expr.app (Expr.app (Expr.sym 18) (inst θ (toTerm (eCode ec)))) (Expr.sym 11))
          (Expr.app (Expr.app (Expr.sym 3) (θ 0)) (Expr.app (Expr.app (Expr.sym 3) (θ 1)) (Expr.sym 2))) = _
      rw [inst_toTerm, first, second]
      rfl
    · cases (Expr.app.inj matched).1

/-- **At the row of a point**: the machine advances, or a halted row with one output starts guessing. -/
theorem rootStep_pointRow {ec : Code} {p : Point} {e' : Expr} (rooted : RootStep (guessSchemas ec) p.row e') :
    (∃ p', Advances p p' ∧ e' = p'.row) ∨ (∃ m, p = .config (.halt [m]) ∧ e' = guessRow m 0) := by
  obtain ⟨pair, member, θ, matched, rfl⟩ := rooted
  rcases List.mem_append.mp member with machine | control
  · exact Or.inl ((rootStep_schemas_iff p _).mp ⟨pair, machine, θ, matched, rfl⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at control
    rcases control with rfl | rfl | rfl
    · rcases row_head p with h | h | h <;> rw [← matched] at h <;> cases h
    · rcases row_head p with h | h | h <;> rw [← matched] at h <;> cases h
    · cases p with
      | normal c' k v => cases (Expr.app.inj matched).1
      | config cfg =>
          cases cfg with
          | ret k v => cases (Expr.app.inj matched).1
          | halt v =>
              have lists : Expr.app (Expr.app (Expr.sym 3) (θ 0)) (Expr.sym 2) = eNats v :=
                (Expr.app.inj matched).2
              cases v with
              | nil => cases lists
              | cons m w =>
                  have parts := Expr.app.inj lists
                  have isNat : θ 0 = eNat m := (Expr.app.inj parts.1).2
                  cases w with
                  | cons b w' => cases parts.2
                  | nil =>
                      refine Or.inr ⟨m, rfl, ?_⟩
                      show Expr.app (Expr.app (Expr.sym 23) (θ 0)) (Expr.sym 0) = guessRow m 0
                      rw [isNat]
                      rfl

/-- The guess grows, as a root rewrite. -/
theorem rootStep_up (ec : Code) (x y : ℕ) : RootStep (guessSchemas ec) (guessRow x y) (guessRow x (y + 1)) :=
  ⟨guessUp, mem_guessUp ec, assign [eNat x, eNat y], rfl, rfl⟩

/-- The guess is checked, as a root rewrite. -/
theorem rootStep_stop (ec : Code) (x y : ℕ) :
    RootStep (guessSchemas ec) (guessRow x y) (Point.normal ec .halt [x, y]).row := by
  refine ⟨guessStop ec, mem_guessStop ec, assign [eNat x, eNat y], rfl, ?_⟩
  show Expr.app (Expr.app (Expr.app (Expr.sym 18) (inst (assign [eNat x, eNat y]) (toTerm (eCode ec))))
      (Expr.sym 11)) (Expr.app (Expr.app (Expr.sym 3) (eNat x)) (Expr.app (Expr.app (Expr.sym 3) (eNat y))
        (Expr.sym 2))) = _
  rw [inst_toTerm]
  rfl

/-- A halted row with one output starts guessing, as a root rewrite. -/
theorem rootStep_restart (ec : Code) (y : ℕ) :
    RootStep (guessSchemas ec) (Point.config (.halt [y])).row (guessRow y 0) :=
  ⟨restartGuess, mem_restartGuess ec, fun _ => eNat y, rfl, rfl⟩

/-- A path of points is a path of root rewrites of the program. -/
theorem rootPath_points (ec : Code) {p q : Point} (path : Relation.ReflTransGen Advances p q) :
    Relation.ReflTransGen (RootStep (guessSchemas ec)) p.row q.row := by
  induction path with
  | refl => exact .refl
  | tail _ advanced reached =>
      obtain ⟨pair, member, θ, matched, made⟩ := (rootStep_schemas_iff _ _).mpr ⟨_, advanced, rfl⟩
      exact reached.tail ⟨pair, List.mem_append_left _ member, θ, matched, made⟩

/-- **The program may guess for ever.** -/
theorem guess_forever (ec : Code) (x : ℕ) : ∀ i, RootStep (guessSchemas ec) (guessRow x i) (guessRow x (i + 1)) :=
  rootStep_up ec x

/-- The guesses from zero reach every guess. -/
theorem guess_path (ec : Code) (x : ℕ) : ∀ y, Relation.ReflTransGen (RootStep (guessSchemas ec)) (guessRow x 0) (guessRow x y)
  | 0 => .refl
  | y + 1 => (guess_path ec x y).tail (rootStep_up ec x y)

/-! ## The may sense at the level of rows -/

/-- **The rows of a number**: its guessing rows; the points of the check of a guess from it, before the check
halts; and the halted row with it as the one output. -/
def GuessRelated (ec : Code) (n : ℕ) (e : Expr) : Prop :=
  (∃ y, e = guessRow n y) ∨
    (∃ y p, e = p.row ∧ Relation.ReflTransGen Advances (.normal ec .halt [n, y]) p ∧
      ∀ w, p ≠ .config (.halt w)) ∨
    e = (Point.config (.halt [n])).row

/-- **The may sense at the level of rows**, for a code that checks guesses for `R`. -/
def rootMay {R : ℕ → ℕ → Prop} {ec : Code} (checks : Checks R ec) :
    MayHosting (equalityGSLT ℕ R) (rootSystem (guessSchemas ec)) where
  related := GuessRelated ec
  readStep := by
    intro n e e' related stepped
    rcases related with ⟨y, rfl⟩ | ⟨y, p, rfl, path, notHalted⟩ | rfl
    · rcases rootStep_guessRow stepped with rfl | rfl
      · exact Or.inl (Or.inl ⟨y + 1, rfl⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨y, .normal ec .halt [n, y], rfl, .refl, fun w same => by cases same⟩))
    · rcases rootStep_pointRow stepped with ⟨p', advanced, rfl⟩ | ⟨m, rfl, -⟩
      · by_cases halted : ∃ w, p' = .config (.halt w)
        · obtain ⟨w, rfl⟩ := halted
          have member : w ∈ ec.eval [n, y] :=
            (eval_iff_runFor ec [n, y] w).mpr (reaches_iff_runFor.mp (path.tail advanced))
          obtain ⟨holds, rfl⟩ := (checks n y w).mp member
          exact Or.inr ⟨y, holds, Or.inr (Or.inr rfl)⟩
        · exact Or.inl (Or.inr (Or.inl ⟨y, p', rfl, path.tail advanced, fun w same => halted ⟨w, same⟩⟩))
      · exact absurd rfl (notHalted [m])
    · rcases rootStep_pointRow (p := .config (.halt [n])) stepped with ⟨p', advanced, -⟩ | ⟨m, same, rfl⟩
      · cases advanced
      · cases same
        exact Or.inl (Or.inl ⟨0, rfl⟩)
  represents n e := e = guessRow n 0
  related_of_represents := fun {_ _} same => Or.inl ⟨0, same⟩
  sound := by
    intro a b e related same
    subst same
    rcases related with ⟨y, same⟩ | ⟨y, p, same, -, -⟩ | same
    · exact (eNat_injective (Expr.app.inj (Expr.app.inj same).1).2).symm
    · rcases row_head p with h | h | h <;> rw [← same] at h <;> cases h
    · cases (Expr.app.inj same).1
  realize := by
    intro a b e represented stepped
    have isGuess : e = guessRow a 0 := represented
    subst isGuess
    have member : [b] ∈ ec.eval [a, b] := (checks a b [b]).mpr ⟨stepped, rfl⟩
    obtain ⟨r, ran⟩ := (eval_iff_runFor ec [a, b] [b]).mp member
    have checked : Relation.ReflTransGen (RootStep (guessSchemas ec)) (Point.normal ec .halt [a, b]).row
        (Point.config (.halt [b])).row := rootPath_points ec (reaches_iff_runFor.mpr ⟨r, ran⟩)
    have path : Relation.ReflTransGen (RootStep (guessSchemas ec)) (guessRow a 0) (guessRow b 0) :=
      (((guess_path ec a b).tail (rootStep_stop ec a b)).trans checked).tail (rootStep_restart ec b)
    exact ⟨guessRow b 0, multiStep_of_steps (S := rootSystem (guessSchemas ec)) path, rfl⟩

/-- **A wrong guess never commits**: when `R n y` fails, the check of `y` from `n` only advances the machine, and
never reaches a halted row. -/
theorem wrong_guess_never_commits {R : ℕ → ℕ → Prop} {ec : Code} (checks : Checks R ec) {n y : ℕ}
    (wrong : ¬ R n y) {e : Expr}
    (path : Relation.ReflTransGen (RootStep (guessSchemas ec)) (Point.normal ec .halt [n, y]).row e) :
    ∃ p, e = p.row ∧ Relation.ReflTransGen Advances (.normal ec .halt [n, y]) p ∧ ∀ w, p ≠ .config (.halt w) := by
  have notHalted : ∀ {p : Point}, Relation.ReflTransGen Advances (.normal ec .halt [n, y]) p →
      ∀ w, p ≠ .config (.halt w) := by
    intro p points w same
    subst same
    have member : w ∈ ec.eval [n, y] := (eval_iff_runFor ec [n, y] w).mpr (reaches_iff_runFor.mp points)
    exact wrong ((checks n y w).mp member).1
  induction path with
  | refl => exact ⟨_, rfl, .refl, notHalted .refl⟩
  | tail _ rooted reached =>
      obtain ⟨p, rfl, points, -⟩ := reached
      rcases rootStep_pointRow rooted with ⟨p', advanced, rfl⟩ | ⟨m, rfl, -⟩
      · exact ⟨p', rfl, points.tail advanced, notHalted (points.tail advanced)⟩
      · exact absurd rfl (notHalted points [m])

/-! ## The may sense on the one-match step -/

/-- **The may sense on the one-match step**: the rows' readback composed with `rootCorrespondence`; a state
represents `n` when it reads as the guessing row `guessRow n 0`. -/
noncomputable def stepMay {R : ℕ → ℕ → Prop} {ec : Code} (checks : Checks R ec) :
    MayHosting (equalityGSLT ℕ R) (stepSystem ℕ (guessRules ec)) where
  toOperationalReadback := (rootMay checks).toOperationalReadback.comp
    (rootCorrespondence (O := ℕ) (guessSchemas_closed ec)).toOperationalReadback
  represents n s := ReadsBag s {guessRow n 0}
  related_of_represents := fun {n _} reads =>
    ⟨guessRow n 0, Or.inl ⟨0, rfl⟩, ({guessRow n 0} : Multiset Expr), rfl, reads⟩
  sound := by
    rintro a b s ⟨e, related, bag, rowBag, reads⟩ readsB
    have isRow : bag = ({e} : Multiset Expr) := rowBag
    subst isRow
    have sameBag : ({e} : Multiset Expr) = {guessRow b 0} :=
      readsAs_unique (ReadsBag.readsAs reads).1 (ReadsBag.readsAs reads).2 (ReadsBag.readsAs readsB).2
    exact (rootMay checks).sound related (Multiset.singleton_inj.mp sameBag)
  realize := by
    intro a b s reads stepped
    obtain ⟨e', run, represented⟩ := (rootMay checks).realize (rfl : guessRow a 0 = guessRow a 0) stepped
    have isGuess : e' = guessRow b 0 := represented
    subst isGuess
    exact firings_of_rootPath (guessSchemas_closed ec) (steps_of_multiStep run) reads

/-- **Every recursively enumerable step relation is hosted in the may sense by a finite program**: `n` reaches
`m` exactly when the program, run from the state of the guessing row `guessRow n 0`, reaches a state that reads
as `guessRow m 0`. -/
theorem hosts_re {R : ℕ → ℕ → Prop} (re : REPred fun p : ℕ × ℕ => R p.1 p.2) :
    ∃ ec : Code, Nonempty (MayHosting (equalityGSLT ℕ R) (stepSystem ℕ (guessRules ec))) ∧
      ∀ a b, Relation.ReflTransGen R a b ↔
        ∃ s', (stepSystem ℕ (guessRules ec)).MultiStep (rowState (guessRow a 0)) s' ∧
          ReadsBag s' {guessRow b 0} := by
  obtain ⟨ec, checks⟩ := exists_check re
  exact ⟨ec, ⟨stepMay checks⟩, fun a b => (stepMay checks).reachable_iff (rowState_reads _) b⟩

/-! ## Control: infinitely many successors -/

/-- **The control**: `0` steps to every number; no other number steps. -/
def fromZero (n : ℕ) (_ : ℕ) : Prop := n = 0

/-- `fromZero` is recursively enumerable, even decidable. -/
theorem fromZero_re : REPred fun p : ℕ × ℕ => fromZero p.1 p.2 := by
  have prim : PrimrecPred fun p : ℕ × ℕ => p.1 = 0 := PrimrecRel.comp Primrec.eq Primrec.fst (Primrec.const 0)
  exact ComputablePred.to_re (PrimrecPred.computablePred prim)

/-- **`fromZero` is hosted in the may sense.** -/
theorem fromZero_may :
    ∃ ec : Code, Nonempty (MayHosting (equalityGSLT ℕ fromZero) (stepSystem ℕ (guessRules ec))) :=
  (hosts_re fromZero_re).imp fun _ both => both.1

/-- **`fromZero` is hosted in the weak sense by no finite program**: `0` has infinitely many successors, and a
weak correspondence to the step of a finite list of range-restricted positive rules, with an observation read
off the bag, gives finitely many. -/
theorem fromZero_not_weak {rules : List SRule} (fragment : ∀ r ∈ rules, RangeRestrictedPositive r)
    (C : WeakCorrespondence (equalityGSLT ℕ fromZero) (stepSystem ℕ rules))
    (showsBag : ∀ {b b' : ℕ} {s s' : SState ℕ} {M : Multiset Expr}, ReadsBag s M → ReadsBag s' M →
      C.shows b s → C.shows b' s' → b = b')
    {s : SState ℕ} {M : Multiset Expr} (related : C.related (0 : ℕ) s) (reads : ReadsBag s M) : False := by
  have finite := successors_finite_of_program fragment C showsBag related reads
  have everything : {b : ℕ | fromZero 0 b} = Set.univ := Set.eq_univ_of_forall fun _ => rfl
  exact (Set.infinite_univ (α := ℕ)) (by rw [← everything]; exact finite)

#print axioms exists_check
#print axioms guess_fragment
#print axioms rootStep_guessRow
#print axioms rootStep_pointRow
#print axioms rootMay
#print axioms wrong_guess_never_commits
#print axioms stepMay
#print axioms hosts_re
#print axioms fromZero_re
#print axioms fromZero_may
#print axioms fromZero_not_weak

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Enumerable
