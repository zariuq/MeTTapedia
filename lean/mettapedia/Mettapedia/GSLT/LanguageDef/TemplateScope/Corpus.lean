import Mettapedia.GSLT.LanguageDef.TemplateScope.Evaluation

/-!
# Template scope, part 4: the corpus

Concrete programs, run by kernel-checked computation (`decide`), giving the
positive and negative examples of each theorem.

Notation: `L = (lam z (let $y z (g $y)))`, `K = (lam z (Pair z $y))`.

* **Theorem 1 (lifting).**  `lifting_positive`: `(let $f L (Pair ($f 1) $y))`
  and the lifted call `(Pair (Lf $y 1) $y)` both answer `(Pair (g 1) 1)`.
  `lifting_negative_B`: under rule B the lambda answers `(Pair (g 1) $y)`.
* **Theorem 2 (inlining).**  `inlining_positive`: the hypothesis of
  `answerBag_elabTopM_inline` holds for `(let $f L (Pair ($f 1) ($f 2)))`.
  `inlining_negative_control`: for
  `(let $f L ((lam w (Pair ($f 1) (let $y w $y))) 5))` hygiene fails;
  re-elaborating the inlined text changes ownership, and the answer
  `(Pair (g 1) 5)` becomes none.
* **Theorem 3 (A fails inlining).**  `ruleA_fails_inlining`.
* **Theorem 4 (B is order-dependent).**  `ruleB_order_dependent` on corpus
  rows 7/8; `ruleB_literal_pair_agrees` records that the literal pair of the
  brief does not separate B (the call happens after `$y := 5` in both
  orders).
* **Theorem 5.**  `lexical_parameter` (`(let $x 5 ((lam $x $x) 6))` gives 6)
  and its negative, a binder-ignoring substitution, which gives 5.
  `observer_moves`: rule B's call-time test is a non-monotone observer;
  moving the call across `$y := 5` changes the answer although the action is
  absorptive.
* **Theorem 6 (occurrence locality).**  `seal_kept`, with the negative
  `spelling_pass_unseals` / `spelling_pass_nonlocal`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.Corpus

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope

/-- Spellings used by the corpus. -/
inductive Sp where
  | f | y | z | w | x | r | t | a | e
  deriving DecidableEq, Repr

/-- Symbols used by the corpus. -/
inductive Sy where
  | Pair | Triple | g | d | ok | no | n1 | n2 | n3 | n4 | n5 | n6 | n7
  | if_ | True_ | never | self | Lf | fe | mk | q
  deriving DecidableEq, Repr

abbrev T := Tm Sy Sp

/-- `$y`. -/
def sv (s : Sp) : T := .var (.src s)
/-- A parameter occurrence. -/
def pv (s : Sp) : T := .pvar (.src s)
/-- A lambda as written (no own binders yet). -/
def lm (s : Sp) (b : T) : T := .lam (.src s) [] b
def ap (f a : T) : T := .app f a
def k (s : Sy) : T := .sym s
def pair (a b : T) : T := ap (ap (k .Pair) a) b
def triple (a b c : T) : T := ap (ap (ap (k .Triple) a) b) c
/-- `(let $s v b)`. -/
def lt (s : Sp) (v b : T) : T := .letP (sv s) v b

/-- No equations. -/
def noProg : Sy → Option T := fun _ => none

/-- `L = (lam z (let $y z (g $y)))`. -/
def L : T := lm .z (lt .y (pv .z) (ap (k .g) (sv .y)))
/-- `K = (lam z (Pair z $y))`. -/
def K : T := lm .z (pair (pv .z) (sv .y))

/-- Answers under rule M. -/
def ansM (prog : Sy → Option T) (t : T) : Option (List T) :=
  answers .static prog 40 (elabTopM t)
/-- Answers under rule A. -/
def ansA (prog : Sy → Option T) (t : T) : Option (List T) :=
  answers .static prog 40 (elabTopA t)
/-- Answers under rule B (no elaboration; copy at the call). -/
def ansB (prog : Sy → Option T) (t : T) : Option (List T) :=
  answers .copyAtCall prog 40 t

/-- `($f 1)`, `($f 2)`. -/
def f1 : T := ap (sv .f) (k .n1)
def f2 : T := ap (sv .f) (k .n2)

/-- A one-name ground store. -/
def store1 (s : Sp) (v : Sy) : GStore Sy Sp := fun n => if n = .src s then some (.sym v) else none

/-! ## Rule M on the brief's desired outputs (C task, tables B and D) -/

/-- B1 `(let $f L (Pair ($f 1) ($f 2)))`. -/
def rowB1 : T := lt .f L (pair f1 f2)
/-- B2 `(Pair (L 1) (L 2))`, the inlined text of B1. -/
def rowB2 : T := pair (ap L (k .n1)) (ap L (k .n2))
/-- B4 `(let $f L (Pair ($f 1) $y))`: a captured name is shared. -/
def rowB4 : T := lt .f L (pair f1 (sv .y))
/-- B5 `(let $f L (Triple ($f 1) ($f 2) $y))`: captured, conflict. -/
def rowB5 : T := lt .f L (triple f1 f2 (sv .y))
/-- B6 `(let $f K (let $y 5 (Pair ($f 1) ($f 2))))`. -/
def rowB6 : T := lt .f K (lt .y (k .n5) (pair f1 f2))
/-- B8 / B9: nested templates, `((lam z (Pair (let $y z $y) ((lam w (let $y w $y)) 3))) n)`. -/
def rowB8 (n : Sy) : T :=
  ap (lm .z (pair (lt .y (pv .z) (sv .y)) (ap (lm .w (lt .y (pv .w) (sv .y))) (k .n3)))) (k n)
/-- B10: output through a closure. -/
def rowB10 : T :=
  lt .f (lm .z (.letP (ap (k .d) (sv .t)) (pv .z) (k .ok)))
    (lt .r (ap (sv .f) (ap (k .d) (k .n7))) (pair (sv .t) (sv .r)))
/-- D1 `(Pair (let $x 1 $x) (let $x 2 $x))`. -/
def rowD1 : T := pair (lt .x (k .n1) (sv .x)) (lt .x (k .n2) (sv .x))
/-- E1: a pattern quotation binds. -/
def rowE1 : T :=
  lt .r (.letP (.pquote (ap (k .q) (sv .a))) (.quote (ap (k .q) (k .n1))) (k .ok))
    (pair (sv .a) (sv .r))

theorem rowB1_M : ansM noProg rowB1 = some [pair (ap (k .g) (k .n1)) (ap (k .g) (k .n2))] := by
  decide
theorem rowB2_M : ansM noProg rowB2 = some [pair (ap (k .g) (k .n1)) (ap (k .g) (k .n2))] := by
  decide
theorem rowB4_M : ansM noProg rowB4 = some [pair (ap (k .g) (k .n1)) (k .n1)] := by decide
theorem rowB5_M : ansM noProg rowB5 = some [] := by decide
theorem rowB6_M :
    ansM noProg rowB6 = some [pair (pair (k .n1) (k .n5)) (pair (k .n2) (k .n5))] := by
  decide
theorem rowB8_M : ansM noProg (rowB8 .n3) = some [pair (k .n3) (k .n3)] := by decide
theorem rowB9_M : ansM noProg (rowB8 .n4) = some [] := by decide
theorem rowB10_M : ansM noProg rowB10 = some [pair (k .n7) (k .ok)] := by decide
theorem rowD1_M : ansM noProg rowD1 = some [] := by decide
theorem rowE1_M : ansM noProg rowE1 = some [pair (k .n1) (k .ok)] := by decide

/-- Rule M records `$y` as `L`'s own name in B1, and as captured in B4. -/
theorem rowB1_B4_ownership :
    elabTopM rowB1 = lt .f (.lam (.src .z) [.y] (lt .y (pv .z) (ap (k .g) (sv .y))))
      (pair f1 f2) ∧
    elabTopM rowB4 = rowB4 := by
  decide

/-! ## Theorem 1: lifting -/

/-- `L` as elaborated in B4: it owns nothing and captures `$y`. -/
def L_B4 : T := lm .z (lt .y (pv .z) (ap (k .g) (sv .y)))

/-- The program holding `L`'s lambda-lifted equation `(= (Lf $y $z) (let $y $z (g $y)))`. -/
def progLf : Sy → Option T := fun s => if s = .Lf then some (lifted [.src .y] L_B4) else none

/-- `(Pair (Lf $y 1) $y)`: B4 with the lambda replaced by its lifted equation. -/
def rowB4lifted : T := pair (ap (callSpine (.fn .Lf) [sv .y]) (k .n1)) (sv .y)

/-- The hypotheses of `run_lifted_call` hold for B4's lambda, its captured
names are exactly `$y`, and the lifted equation is closed. -/
theorem lifting_hypotheses :
    captured L_B4 = [.src .y] ∧ elabTopM rowB4 = lt .f L_B4 (pair f1 (sv .y)) ∧
    [Nm.src Sp.y].Nodup ∧ (∀ c ∈ [Nm.src Sp.y], c ∉ paramNames L_B4) ∧
    freeNames (lifted [.src .y] L_B4) = [] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **Theorem 1, positive.**  The lambda and its lifted equation agree on
B4, as the general theorem says for every argument and store. -/
theorem lifting_positive :
    ansM noProg rowB4 = some [pair (ap (k .g) (k .n1)) (k .n1)] ∧
    answers .static progLf 40 rowB4lifted = some [pair (ap (k .g) (k .n1)) (k .n1)] ∧
    ∀ (n : ℕ), 4 ≤ n → ∀ (a : T) (π : Path) (σ : GStore Sy Sp),
      run .static progLf n π σ (.app (callSpine (.fn .Lf) [sv .y]) a) =
        run .static progLf n π σ (.app L_B4 a) := by
  refine ⟨by decide, by decide, ?_⟩
  intro n hn a π σ
  exact run_lifted_call progLf .Lf [.src .y] (.src .z) [] _ a rfl (by decide)
    (by decide) n hn π σ

/-- **Theorem 1, negative (rule B).**  Copying at the call, the lambda copies
the captured `$y`, which its lifted equation shares: `(Pair (g 1) $y)`
against `(Pair (g 1) 1)`. -/
theorem lifting_negative_B :
    ansB noProg rowB4 = some [pair (ap (k .g) (k .n1)) (sv .y)] ∧
    ansB noProg rowB4 ≠ answers .static progLf 40 rowB4lifted := by
  decide

/-! ## Theorem 2: inlining -/

/-- The text inlining of B1 is B2. -/
theorem rowB2_is_inlined :
    rowB2 = subst (Sub.single (.src .f) L) Sub.none (pair f1 f2) := by
  decide

/-- **Theorem 2, positive.**  B1 satisfies the hygiene hypothesis, so the
general theorem gives equal answer bags for B1 and its inlined text B2. -/
theorem inlining_positive (bag : List T) :
    AnswerBag .static noProg (elabTopM rowB1) bag ↔
      AnswerBag .static noProg (elabTopM rowB2) bag := by
  rw [rowB2_is_inlined]
  exact answerBag_elabTopM_inline noProg .f (.src .z) _ (pair f1 f2) (by decide)
    (by decide) (by decide) bag

/-- The context of the negative control: `((lam w (Pair ($f 1) (let $y w $y))) 5)`. -/
def ctxW : T := ap (lm .w (pair f1 (lt .y (pv .w) (sv .y)))) (k .n5)
/-- `(let $f L ((lam w (Pair ($f 1) (let $y w $y))) 5))`. -/
def rowW : T := lt .f L ctxW
/-- Its inlined text `((lam w (Pair (L 1) (let $y w $y))) 5)`. -/
def rowWinl : T := subst (Sub.single (.src .f) L) Sub.none ctxW

/-- **Theorem 2, negative control.**  The two lambdas are disjoint, so each
owns `$y`, and the answer is `(Pair (g 1) 5)`; the evaluator's own
substitution of the elaborated `L` keeps it.  Re-elaborating the inlined
text puts `L` inside a scope that writes `$y`: `L` captures it, ownership
changes, and there is no answer.  Exactly the hygiene hypothesis fails. -/
theorem inlining_negative_control :
    ansM noProg rowW = some [pair (ap (k .g) (k .n1)) (k .n5)] ∧
    answers .static noProg 40
        (subst (Sub.single (.src .f) (elabM (direct rowW) L)) Sub.none
          (elabM (direct rowW) ctxW)) = some [pair (ap (k .g) (k .n1)) (k .n5)] ∧
    ansM noProg rowWinl = some [] ∧
    elabTopM rowWinl ≠
      subst (Sub.single (.src .f) (elabM (direct rowW) L)) Sub.none
        (elabM (direct rowW) ctxW) ∧
    hygM .f (names (lt .y (pv .z) (ap (k .g) (sv .y)))) (elabM (direct rowW) ctxW) = false := by
  decide

/-! ## Theorem 3: rule A fails inlining -/

/-- **Theorem 3.**  Under rule A, one lambda applied at two sites answers
`(Pair (g 1) (g 2))`; after inlining, the two copies' `$y` is quantified at
the query, shared, and conflicts: no answer.  Rule M answers both. -/
theorem ruleA_fails_inlining :
    ansA noProg rowB1 = some [pair (ap (k .g) (k .n1)) (ap (k .g) (k .n2))] ∧
    ansA noProg rowB2 = some [] ∧
    ansM noProg rowB1 = ansM noProg rowB2 := by
  decide

/-- Rule A also loses the negative control's answer before inlining. -/
theorem ruleA_rowW : ansA noProg rowW = some [] := by decide

/-! ## Theorem 4: rule B is order-dependent -/

/-- The brief's pair `(let $f K (let $y 5 ($f 1)))` and its swap. -/
def litB : T := lt .f K (lt .y (k .n5) f1)
def litB' : T := lt .y (k .n5) (lt .f K f1)

/-- Corpus rows 7 and 8: the call before, and after, `$y := 5`. -/
def row7 : T := lt .f K (lt .r f1 (lt .y (k .n5) (sv .r)))
def row8 : T := lt .f K (lt .y (k .n5) (lt .r f1 (sv .r)))

/-- The literal pair of the brief does not separate rule B: in both orders the
call happens after `$y := 5`. -/
theorem ruleB_literal_pair_agrees :
    ansB noProg litB = some [pair (k .n1) (k .n5)] ∧
    ansB noProg litB' = some [pair (k .n1) (k .n5)] ∧
    ansM noProg litB = some [pair (k .n1) (k .n5)] ∧
    ansM noProg litB' = some [pair (k .n1) (k .n5)] := by
  decide

/-- **Theorem 4.**  Swapping the two `let`s of row 7 changes rule B's answer:
the call before the binding copies `$y`, and the binding never reaches the
copy.  Rule M answers both with `(Pair 1 5)`. -/
theorem ruleB_order_dependent :
    ansB noProg row7 = some [pair (k .n1) (.var (.inst [0, 2] (.src .y)))] ∧
    ansB noProg row8 = some [pair (k .n1) (k .n5)] ∧
    ansM noProg row7 = some [pair (k .n1) (k .n5)] ∧
    ansM noProg row8 = some [pair (k .n1) (k .n5)] := by
  decide

/-! ## Theorem 5: the environment action -/

/-- `(let $x 5 ((lam $x $x) 6))`: the parameter `$x` is lexical. -/
def rowX : T := lt .x (k .n5) (ap (.lam (.src .x) [] (pv .x)) (k .n6))

/-- A binder-ignoring substitution of a spelling (the class of audit
finding 3): it fills parameter occurrences of the same spelling too. -/
def fillBySpelling (s : Sp) (v : T) : T → T
  | .var n => if n = .src s then v else .var n
  | .pvar x => if x = .src s then v else .pvar x
  | .lam x own b => .lam x own (fillBySpelling s v b)
  | .app f a => .app (fillBySpelling s v f) (fillBySpelling s v a)
  | .quote c => .quote (fillBySpelling s v c)
  | .pquote c => .pquote (fillBySpelling s v c)
  | .letP p w b => .letP (fillBySpelling s v p) (fillBySpelling s v w) (fillBySpelling s v b)
  | .alt t₁ t₂ => .alt (fillBySpelling s v t₁) (fillBySpelling s v t₂)
  | t => t

/-- **Theorem 5, the lexical example.**  The answer is 6 under every rule; the
action leaves the lambda alone.  A binder-ignoring substitution gives 5. -/
theorem lexical_parameter :
    ansM noProg rowX = some [k .n6] ∧ ansA noProg rowX = some [k .n6] ∧
    ansB noProg rowX = some [k .n6] ∧
    act (store1 .x .n5) (ap (.lam (.src .x) [] (pv .x)) (k .n6)) =
      ap (.lam (.src .x) [] (pv .x)) (k .n6) ∧
    answers .static noProg 40
        (fillBySpelling .x (k .n5) (ap (.lam (.src .x) [] (pv .x)) (k .n6))) =
      some [k .n5] := by
  decide

/-- Absorption needs `σ ⊑ τ`: an overwrite of `$x` is not absorbed. -/
theorem absorb_needs_refinement :
    act (store1 .x .n6) (act (store1 .x .n5) (sv .x)) ≠ act (store1 .x .n6) (sv .x) := by
  decide

/-- Idempotence needs ground values: a substitution whose value mentions a
store name bound by the same substitution is not idempotent. -/
theorem idem_needs_ground :
    let θ : Sub Sy Sp := fun n =>
      if n = .src .x then some (sv .y) else if n = .src .y then some (k .n1) else none
    subst θ Sub.none (subst θ Sub.none (sv .x)) ≠ subst θ Sub.none (sv .x) := by
  decide

/-- A toy metatype observer: is the term, under the store, still a variable? -/
def isVarObs (σ : GStore Sy Sp) (t : T) : Bool :=
  match act σ t with
  | .var _ => true
  | _ => false

/-- **No scheduling independence.**  The action is absorptive, yet an
observer moved across a refinement sees something else: the toy observer, and
rule B's call-time test in-language (rows 7 and 8, `ruleB_order_dependent`). -/
theorem observer_moves :
    act (store1 .y .n5) (act Store.empty (sv .y)) = act (store1 .y .n5) (sv .y) ∧
    isVarObs Store.empty (sv .y) = true ∧ isVarObs (store1 .y .n5) (sv .y) = false ∧
    ansB noProg row7 ≠ ansB noProg row8 := by
  decide

/-! ## Theorem 6: occurrence locality -/

/-- `(if True @$x (match &self @(never $s) no))`, the match written as a `let`
with a pattern quotation. -/
def ifSeal (s : Sp) : T :=
  ap (ap (ap (k .if_) (k .True_)) (.quote (sv .x)))
    (.letP (.pquote (ap (k .never) (sv s))) (k .self) (k .no))

/-- Names written inside pattern quotations anywhere in a term. -/
def pqNames : T → List (Nm Sp)
  | .pquote c => freeNames c
  | .lam _ _ b => pqNames b
  | .app f a => pqNames f ++ pqNames a
  | .letP p w b => pqNames p ++ pqNames w ++ pqNames b
  | .alt t₁ t₂ => pqNames t₁ ++ pqNames t₂
  | _ => []

/-- The spelling-based seal (the draft's bug class): a name that is a pattern
hole anywhere is filled everywhere, sealed quotations included. -/
def fillHolesBySpelling (H : List (Nm Sp)) (σ : GStore Sy Sp) : T → T
  | .quote c => .quote (act (fun n => if n ∈ H then σ n else none) c)
  | .var n => act σ (.var n)
  | .lam x own b => .lam x own (fillHolesBySpelling H (σ.hide own) b)
  | .app f a => .app (fillHolesBySpelling H σ f) (fillHolesBySpelling H σ a)
  | .pquote c => .pquote (act σ c)
  | .letP p w b =>
      .letP (fillHolesBySpelling H σ p) (fillHolesBySpelling H σ w) (fillHolesBySpelling H σ b)
  | .alt t₁ t₂ => .alt (fillHolesBySpelling H σ t₁) (fillHolesBySpelling H σ t₂)
  | t => t

/-- The spelling-based action on a whole term. -/
def actBySpelling (σ : GStore Sy Sp) (t : T) : T := fillHolesBySpelling (pqNames t) σ t

/-- **Theorem 6, positive.**  The action keeps `@$x` sealed and fills the
pattern hole of the dead branch. -/
theorem seal_kept :
    act (store1 .x .n5) (ifSeal .x) =
      ap (ap (ap (k .if_) (k .True_)) (.quote (sv .x)))
        (.letP (.pquote (ap (k .never) (k .n5))) (k .self) (k .no)) := by
  decide

/-- **Theorem 6, negative.**  The spelling-based pass unseals `@$x` because a
dead branch writes `$x` in a pattern; with `$z` there instead, it does not.
The sibling decides, which locality forbids. -/
theorem spelling_pass_nonlocal :
    actBySpelling (store1 .x .n5) (ifSeal .x) =
      ap (ap (ap (k .if_) (k .True_)) (.quote (k .n5)))
        (.letP (.pquote (ap (k .never) (k .n5))) (k .self) (k .no)) ∧
    actBySpelling (store1 .x .n5) (ifSeal .z) =
      ap (ap (ap (k .if_) (k .True_)) (.quote (sv .x)))
        (.letP (.pquote (ap (k .never) (sv .z))) (k .self) (k .no)) := by
  decide

/-- The sealed hole of `ifSeal`, as a context: the general theorem
`act_hole_local` applies to any two siblings. -/
theorem seal_hole_local (s s' : Sp) :
    holeAct (store1 .x .n5)
        ([Frame.appR (ap (ap (k .if_) (k .True_)) (.quote (sv .x))), Frame.appL
            (.letP (.pquote (ap (k .never) (sv s))) (k .self) (k .no)), Frame.quoteC].map
          Frame.kind) (sv .x) =
      holeAct (store1 .x .n5)
        ([Frame.appR (ap (ap (k .if_) (k .True_)) (.quote (sv .x))), Frame.appL
            (.letP (.pquote (ap (k .never) (sv s'))) (k .self) (k .no)), Frame.quoteC].map
          Frame.kind) (sv .x) :=
  act_hole_local _ rfl _

end Mettapedia.GSLT.LanguageDef.TemplateScope.Corpus
