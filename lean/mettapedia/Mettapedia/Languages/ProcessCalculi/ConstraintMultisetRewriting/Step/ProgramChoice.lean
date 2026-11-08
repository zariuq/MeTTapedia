import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramReflection

/-!
# Shared versus independent choice

A choice `amb l r` is one step, so on the step one firing (`ambL` or `ambR`). A **shared choice** is
bound once by a `let`: the program chooses once and every use of the bound name reads the one value
the binding firing put in the scope. An **independent choice** sits in a closure: each call
evaluates the closure's body again, so each use is a separate choice firing.

* `shared`: `let x = amb a b in (use x, use x)`. Every run makes one choice (one choice
  configuration is reachable, `shared_one_choice`), and every halted run has two agreeing uses
  (`shared_uses_agree`); both values are possible.
* `independent`: `let f = λ_. amb a b in (use (f u), use (f u))`. Each call is a separate choice (three
  choice configurations are reachable, `independent_separate_choices`), and a halted run has
  disagreeing uses (`independent_uses_disagree`).
* **The observational separation** (`shared_vs_independent`), on the step too
  (`shared_vs_independent_on_step`): every halted translated run of the shared program represents
  agreeing uses, and some halted translated run of the independent program represents disagreeing
  ones.

The two uses are observed in the final closure's scope: `lam (var 0)` returns a closure capturing the
scope in which both uses were bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program

open ProgramRows ProgramTranslation

/-- A configuration evaluating a choice. -/
def isChoice : Sx → Bool
  | .cell (.sym 29) (.cell (.cell (.sym 11) _) _) => true
  | _ => false

/-- The two most recent bindings of a returned closure agree. -/
def usesAgree : List Sx → Bool
  | [.cell (.sym 30) (.cell (.cell (.sym 18) (.cell _ (.cell (.sym 21) (.cell v (.cell (.sym 21) (.cell w _)))))) _)] =>
      v == w
  | _ => false

/-- The two most recent bindings of a returned closure differ. -/
def usesDisagree : List Sx → Bool
  | [.cell (.sym 30) (.cell (.cell (.sym 18) (.cell _ (.cell (.sym 21) (.cell v (.cell (.sym 21) (.cell w _)))))) _)] =>
      v != w
  | _ => false

/-- **Shared choice**: `let x = amb a b in let y = x in λ. var 0`. -/
def shared : Sx := ev (let_ (amb (atom ka) (atom kb)) (let_ (var zero) (lam (var zero)))) nil nil

/-- **Independent choice**: `let f = λ. amb a b in let x = f u in let y = f u in λ. var 0`. -/
def independent : Sx :=
  ev (let_ (lam (amb (atom ka) (atom kb)))
    (let_ (app (var zero) (atom ku)) (let_ (app (var (succ zero)) (atom ku)) (lam (var zero))))) nil nil

theorem shared_closed : SuccessorClosed (reach 12 [[shared]]) = true := by decide
theorem independent_closed : SuccessorClosed (reach 30 [[independent]]) = true := by decide

/-- **A shared choice is one choice**: exactly one reachable configuration evaluates a choice. -/
theorem shared_one_choice :
    ((reach 12 [[shared]]).filter fun W => W.any isChoice).length = 1 := by decide

/-- **Independent choices are separate choices**: three reachable configurations evaluate a choice,
the first call's and the second call's after either first value. -/
theorem independent_separate_choices :
    ((reach 30 [[independent]]).filter fun W => W.any isChoice).length = 3 := by decide

/-- The shared program halts at both values, each with agreeing uses. -/
theorem shared_halted :
    halted (reach 12 [[shared]]) =
      [[ret (clo (var zero) (cons (atom ka) (cons (atom ka) nil))) nil],
        [ret (clo (var zero) (cons (atom kb) (cons (atom kb) nil))) nil]] := by decide

/-- **Two uses of a shared binding always agree**, in every halted run. -/
theorem shared_uses_agree (W : Multiset Sx) (path : Relation.ReflTransGen Step ({shared} : Multiset Sx) W)
    (stuck : ∀ W', ¬ Step W W') : ∃ H : List Sx, W = (H : Multiset Sx) ∧ usesAgree H = true := by
  obtain ⟨H, mem, rfl⟩ := (halted_runs shared_closed).2 W path stuck
  refine ⟨H, rfl, ?_⟩
  have all : (halted (reach 12 [[shared]])).all usesAgree = true := by decide
  exact List.all_eq_true.mp all H mem

/-- The run of the independent program whose two calls choose differently. -/
def disagreeing : List Sx :=
  [ret (clo (var zero) (cons (atom kb) (cons (atom ka) (cons (clo (amb (atom ka) (atom kb)) nil) nil)))) nil]

theorem disagreeing_halted : disagreeing ∈ halted (reach 30 [[independent]]) := by decide

/-- **Independent uses can disagree**: a halted run calls the closure twice and gets two values. -/
theorem independent_uses_disagree :
    Relation.ReflTransGen Step ({independent} : Multiset Sx) (disagreeing : Multiset Sx) ∧
      (∀ W', ¬ Step (disagreeing : Multiset Sx) W') ∧ usesDisagree disagreeing = true :=
  ⟨((halted_runs independent_closed).1 _ disagreeing_halted).1,
    ((halted_runs independent_closed).1 _ disagreeing_halted).2, by decide⟩

/-- **The observational separation of shared and independent choice.** -/
theorem shared_vs_independent :
    (∀ W, Relation.ReflTransGen Step ({shared} : Multiset Sx) W → (∀ W', ¬ Step W W') →
        ∃ H : List Sx, W = (H : Multiset Sx) ∧ usesAgree H = true) ∧
      ∃ H : List Sx, Relation.ReflTransGen Step ({independent} : Multiset Sx) (H : Multiset Sx) ∧
        (∀ W', ¬ Step (H : Multiset Sx) W') ∧ usesDisagree H = true :=
  ⟨shared_uses_agree, disagreeing, independent_uses_disagree⟩

/-- **The separation on the step.** Every translated run of the shared program that has no further
firing represents agreeing uses; a translated run of the independent program reaches a configuration
with no further firing that represents disagreeing uses. -/
theorem shared_vs_independent_on_step :
    (∀ q : Config × ℕ, Relation.ReflTransGen (Translated schema) (initial [shared], 1) q →
        (∀ q', ¬ Translated schema q q') → ∃ H : List Sx, Represents q.1 (H : Multiset Sx) q.2 ∧ usesAgree H = true) ∧
      ∃ q : Config × ℕ, Relation.ReflTransGen (Translated schema) (initial [independent], 1) q ∧
        (∀ q', ¬ Translated schema q q') ∧ Represents q.1 (disagreeing : Multiset Sx) q.2 ∧
          usesDisagree disagreeing = true := by
  refine ⟨fun q run stuck => ?_, ?_⟩
  · obtain ⟨H, mem, rep⟩ := halted_on_step shared_closed run stuck
    have all : (halted (reach 12 [[shared]])).all usesAgree = true := by decide
    exact ⟨H, rep, List.all_eq_true.mp all H mem⟩
  · obtain ⟨path, stuck, disagree⟩ := independent_uses_disagree
    obtain ⟨q, run, rep⟩ := path_on_step path (initial_represents [independent])
    exact ⟨q, run, fun q' firing => stuck_of_source rep stuck q' firing, rep, disagree⟩

#print axioms shared_one_choice
#print axioms independent_separate_choices
#print axioms shared_halted
#print axioms shared_uses_agree
#print axioms disagreeing_halted
#print axioms independent_uses_disagree
#print axioms shared_vs_independent
#print axioms shared_vs_independent_on_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program
