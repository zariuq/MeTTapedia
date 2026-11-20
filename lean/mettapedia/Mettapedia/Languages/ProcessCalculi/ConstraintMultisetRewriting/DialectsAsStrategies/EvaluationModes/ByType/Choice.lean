import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.ByType.Transfer

/-!
# Alternatives: one shared choice, or two independent ones

The core already answers with a list read as a bag: a head with several matching equations, such
as `(= (two) 1) (= (two) 2)`, is a choice between alternatives, and `bind` continues every answer.
No second evaluator is needed; every general theorem of this folder is over programs with such
heads, so the laws of `Laws` and `Transfer` hold with alternatives (witnesses below).

**The duplication law** (`(: dup (-> X R)) (= (dup $x) (pair $x $x))`, `R` an unchecked value type):

* `dup_value`: a parameter of an unchecked value type `T` is one choice shared by its occurrences:
  `(dup M)` answers `(pair v v)` for each answer `v` of `M`.
* `dup_held`: held text (`Atom` or `(Code T)`) is run at each occurrence, two independent choices:
  `(dup M)` answers `(pair v w)` for each answer `v` and each answer `w` of `M`.

Both hold for every program and every term `M` whose run finishes refusing nothing; the bag
statements compare multisets. The control `(two)` gives two pairs and four pairs (`dup_two_rows`), as
measured: HE `[(pair 1 1), (pair 1 2), (pair 2 1), (pair 2 2)]` for an `Atom` parameter and two
equal pairs for `%Undefined%`, `Number` and undeclared parameters; the PeTTa lane and the Prime
draft `(pair (two) (two))` for `Atom` (their held text is inert: `codeOnly`), two equal pairs
otherwise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core CoreLaws Typed Acceptance

namespace ByType

/-! ## Continuing every answer -/

/-- The answers of `bind` with a continuation that always answers. -/
def cont (f : Atom → List Ans) (L : List Ans) : List Ans :=
  L.flatMap fun a => match a with
    | (.val v, tr) => (f v).map fun c => (c.1, tr ++ c.2)
    | (.refused d k, tr) => [(.refused d k, tr)]

theorem continueEach_total (f : Atom → List Ans) :
    ∀ L : List Ans, continueEach (fun v => some (f v)) L = some (cont f L)
  | [] => rfl
  | (.val v, tr) :: rest => by
      simp [continueEach, cont, continueEach_total f rest]
  | (.refused d k, tr) :: rest => by
      simp [continueEach, cont, continueEach_total f rest]

theorem observe_append (b : Bool) : ∀ L L' : List Ans,
    observe b (L ++ L') = observe b L ++ observe b L'
  | [], _ => rfl
  | (.val v, tr) :: rest, L' => by simp [observe, observe_append b rest L']
  | (.refused d k, tr) :: rest, L' => by
      cases b <;> simp [observe, observe_append _ rest L']

theorem observe_retrace (b : Bool) (tr : List String) : ∀ X : List Ans,
    observe b (X.map fun c => (c.1, tr ++ c.2)) = observe b X
  | [] => rfl
  | (.val v, t) :: rest => by simp [observe, observe_retrace b tr rest]
  | (.refused d k, t) :: rest => by
      cases b <;> simp [observe, observe_retrace _ tr rest]

/-- Printed, continuing every value answer is a flat map over the printed values. -/
theorem observe_cont (b : Bool) (f : Atom → List Ans) : ∀ L : List Ans, allVal L = true →
    observe b (cont f L) = (observe b L).flatMap fun v => observe b (f v)
  | [], _ => rfl
  | (.val v, tr) :: rest, h => by
      simp only [allVal_cons, Out.isVal, Bool.true_and] at h
      have := observe_cont b f rest h
      simp only [cont, List.flatMap_cons] at this ⊢
      rw [observe_append, observe_retrace, this]
      simp [observe]
  | (.refused d k, tr) :: rest, h => by
      simp [allVal, Out.isVal] at h

/-! ## The programs -/

/-- `(= (two) 1) (= (two) 2)`. -/
def twoT : TFn := ⟨"two", none, [([], N 1), ([], N 2)]⟩

/-- `(: dup (-> X R)) (= (dup $x) (pair $x $x))`. -/
def dupT (X R : CTy) : TFn := heldBodyT "dup" X R (E [S "pair", V "x", V "x"])

/-- `(dup M)`. -/
def dupQ (M : Atom) : Atom := E [S "dup", M]

/-- `(pair v w)`. -/
def pairOf (v w : Atom) : Atom := .expression [.symbol "pair", v, w]

/-- The body of `dup` in the core: each occurrence runs the text (held parameter) or is the value
(value parameter). -/
def dupBody (runs : Bool) : Comp :=
  let occ : Comp := if runs then .run (.var "x") else .ret (.var "x")
  .bind occ (slot 0) (.bind occ (slot 1)
    (.ret (.expression [.symbol "pair", .var (slot 0), .var (slot 1)])))

theorem modeView_none {P : TProg} {h : String} {n : Nat} (hn : tmodesOf P h n = none) :
    modeView (tmodesOf P) h n = none := by
  simp [modeView, hn]

theorem dup_clauses {X R : CTy} (hR : R.holds = false) (P0 : TProg)
    (hpair : tmodesOf (dupT X R :: P0) "pair" 2 = none) :
    (elabFnB byType (tmodesOf (dupT X R :: P0)) (dupT X R)).clauses =
      [([.var "x"], dupBody X.holds)] := by
  show [([Atom.var "x"], bodyB byType (tmodesOf (dupT X R :: P0)) (heldTyped [X] [V "x"])
    (heldNames [X] [V "x"]) R (E [S "pair", V "x", V "x"]))] = _
  rw [bodyB_value _ _ _ _ hR]
  unfold elabV
  rw [show (E [S "pair", V "x", V "x"] : Atom) =
      .expression [.symbol "pair", .var "x", .var "x"] from rfl,
    elabW.eq_5 _ _ _ _ _ _ (by intros; simp_all) (by intros; simp_all) (by intros; simp_all)]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    modeView_none hpair]
  rw [show List.replicate 2 CTy.undef = [.undef, .undef] from rfl,
    elabArgsW_value _ _ _ rfl, elabArgsW_value _ _ _ rfl]
  cases hX : X.holds
  · have hn : heldNames [X] [V "x"] = [] := by simp [heldNames, hX]
    simp [hn, elabW, dupBody, elabArgsW]
  · have hn : heldNames [X] [V "x"] = ["x"] := by simp [heldNames, hX, patVars, V]
    simp [hn, elabW, dupBody, elabArgsW, rdOf_byType, CTy.holds]

theorem find_dupT (X R : CTy) (P0 : TProg) :
    (elabProgB byType (dupT X R :: P0)).find "dup" 1 =
      some (elabFnB byType (tmodesOf (dupT X R :: P0)) (dupT X R)) := by
  simp [Prog.find, elabProgB, dupT, heldBodyT, elabFnB, TFn.arity]

/-- Entering `dup` with an argument runs its body with `$x` bound to it, marking every answer. -/
theorem exec_enter_dup {X R : CTy} (hR : R.holds = false) (hRc : R.check = none)
    (hXc : X.check = none) (P0 : TProg)
    (hpair : tmodesOf (dupT X R :: P0) "pair" 2 = none) (a : Atom) (k : Nat) :
    exec (elabProgB byType (dupT X R :: P0)) (k + 1) (.enter "dup" [a]) =
      (exec (elabProgB byType (dupT X R :: P0)) k (.comp [("x", a)] (dupBody X.holds))).map
        (List.map (Laws.prefixTrace "dup")) :=
  Laws.exec_enter_first _ "dup" [a] _ [.var "x"] _ [] [("x", a)] k (find_dupT X R P0)
    (by simp [elabFnB, dupT, heldBodyT, TFn.params, firstRefusal, hXc])
    (by simp [elabFnB, dupT, heldBodyT, TFn.result, hRc]) (dup_clauses hR P0 hpair) rfl
    fun _ => rfl

theorem inst_pair (v w a : Atom) :
    inst [(slot 1, w), (slot 0, v), ("x", a)]
        (.expression [.symbol "pair", .var (slot 0), .var (slot 1)]) = pairOf v w := by
  simp [inst, inst.instList, slot, pairOf, List.lookup]

/-! ## The value parameter: one shared choice -/

theorem queryB_dup_value {T R : CTy} (hT : T.holds = false) (P0 : TProg) (M : Atom) :
    queryB byType (dupT T R :: P0) (dupQ M) =
      .bind (queryB byType (dupT T R :: P0) M) (slot 0) (.call "dup" [.var (slot 0)]) := by
  have hms : modeView (tmodesOf (dupT T R :: P0)) "dup" 1 = some [eraseTy T] := by
    simp [modeView, tmodesOf, dupT, heldBodyT, TFn.arity, TFn.params]
  unfold queryB elabV dupQ
  rw [show (E [S "dup", M] : Atom) = .expression [.symbol "dup", M] from rfl,
    elabW.eq_5 _ _ _ _ _ _ (by intros; simp_all) (by intros; simp_all) (by intros; simp_all)]
  simp only [List.length_singleton, hms]
  rw [elabArgsW_value _ _ _ (by rw [eraseTy_holds]; exact hT), eraseTy_value hT]
  have h1 : rdOf byType [] T = rdOf byType [] .undef := by
    rw [rdOf_byType]
    funext x
    show (!T.holds) = (!CTy.undef.holds)
    rw [hT]
    rfl
  rw [h1]
  rfl

/-- **A value parameter is one choice shared by its occurrences**: for each answer `v` of `M`,
`(dup M)` answers `(pair v v)`. -/
theorem dup_value {T R : CTy} (hT : UncheckedT T) (hR : R.holds = false) (hRc : R.check = none)
    (P0 : TProg) (hpair : tmodesOf (dupT T R :: P0) "pair" 2 = none) (M : Atom) (m : Nat) :
    runB byType (dupT T R :: P0) (m + 6) (dupQ M) =
      (runB byType (dupT T R :: P0) (m + 5) M).map
        (cont fun v => [(.val (pairOf v v), ["dup"])]) := by
  obtain ⟨hv, hc⟩ := uncheckedT_value hT
  have hk : (fun v => exec (elabProgB byType (dupT T R :: P0)) (m + 5)
      (.comp [(slot 0, v)] (.call "dup" [.var (slot 0)]))) =
      fun v => some [(.val (pairOf v v), ["dup"])] := by
    funext v
    rw [exec_call]
    simp only [List.map, inst_var_head]
    rw [exec_enter_dup hR hRc hc P0 hpair v (m + 3)]
    simp only [dupBody, hv, Bool.false_eq_true, if_false]
    rw [Laws.exec_bind_ret_val, Laws.exec_bind_ret_val, exec_ret]
    simp [inst, inst.instList, slot, pairOf, List.lookup, Laws.prefixTrace]
  unfold runB
  rw [queryB_dup_value hv P0 M, exec_bind, hk]
  cases exec _ (m + 5) _ with
  | none => rfl
  | some L => exact continueEach_total _ L

/-! ## Held text: two independent choices -/

theorem queryB_dup_held {X R : CTy} (hX : X.holds = true) (P0 : TProg) (M : Atom) :
    queryB byType (dupT X R :: P0) (dupQ M) = .call "dup" [M] := by
  have hms : modeView (tmodesOf (dupT X R :: P0)) "dup" 1 = some [eraseTy X] := by
    simp [modeView, tmodesOf, dupT, heldBodyT, TFn.arity, TFn.params]
  unfold queryB elabV dupQ
  rw [show (E [S "dup", M] : Atom) = .expression [.symbol "dup", M] from rfl,
    elabW.eq_5 _ _ _ _ _ _ (by intros; simp_all) (by intros; simp_all) (by intros; simp_all)]
  simp only [List.length_singleton, hms]
  rw [elabArgsW_held _ _ _ (by rw [eraseTy_holds]; exact hX)]
  rfl

/-- **Held text is run at each occurrence**: for each answer `v` and each answer `w` of `M`,
`(dup M)` answers `(pair v w)`. -/
theorem dup_held {X R : CTy} (hX : X.holds = true) (hR : R.holds = false) (hRc : R.check = none)
    (P0 : TProg) (hpair : tmodesOf (dupT X R :: P0) "pair" 2 = none) (M : Atom) (m : Nat)
    (L : List Ans) (hM : runB byType (dupT X R :: P0) m M = some L) :
    runB byType (dupT X R :: P0) (m + 5) (dupQ M) =
      some ((cont (fun v => cont (fun w => [(.val (pairOf v w), [])]) L) L).map
        (Laws.prefixTrace "dup")) := by
  have hM1 : runB byType (dupT X R :: P0) (m + 1) M = some L := runB_mono (by omega) hM
  have hcode : ∀ ρ : Env, (inst ρ (.var "x") = M) → ∀ j, m ≤ j →
      exec (elabProgB byType (dupT X R :: P0)) (j + 1) (.comp ρ (.run (.var "x"))) = some L := by
    intro ρ hρ j hj
    rw [exec_run_text, hρ]
    exact runB_mono hj hM
  unfold runB
  rw [queryB_dup_held hX P0 M, exec_call]
  simp only [List.map, inst_nil]
  rw [exec_enter_dup hR hRc (check_of_holds hX) P0 hpair M (m + 3)]
  simp only [dupBody, hX, if_true]
  rw [exec_bind, hcode [("x", M)] (by simp [inst, List.lookup]) (m + 1) (by omega)]
  simp only [Option.bind_some]
  have hk : (fun v => exec (elabProgB byType (dupT X R :: P0)) (m + 2)
      (.comp [(slot 0, v), ("x", M)] (.bind (.run (.var "x")) (slot 1)
        (.ret (.expression [.symbol "pair", .var (slot 0), .var (slot 1)]))))) =
      fun v => some (cont (fun w => [(.val (pairOf v w), [])]) L) := by
    funext v
    rw [exec_bind, hcode [(slot 0, v), ("x", M)] (by simp [inst, List.lookup, slot]) m le_rfl]
    simp only [Option.bind_some]
    have hr : (fun w => exec (elabProgB byType (dupT X R :: P0)) (m + 1)
        (.comp [(slot 1, w), (slot 0, v), ("x", M)]
          (.ret (.expression [.symbol "pair", .var (slot 0), .var (slot 1)])))) =
        fun w => some [(.val (pairOf v w), [])] := by
      funext w
      rw [exec_ret, inst_pair]
    rw [hr]
    exact continueEach_total _ L
  rw [hk, continueEach_total]
  rfl

/-! ## The printed bags -/

theorem flatMap_single (f : Atom → Atom) : ∀ l : List Atom, l.flatMap (fun v => [f v]) = l.map f
  | [] => rfl
  | a :: l => by simp [flatMap_single f l]

/-- With `M` printing the values `vs`, the value parameter prints the diagonal. -/
theorem dup_value_printed {T R : CTy} (hT : UncheckedT T) (hR : R.holds = false)
    (hRc : R.check = none) (P0 : TProg) (hpair : tmodesOf (dupT T R :: P0) "pair" 2 = none)
    (M : Atom) (m : Nat) (L : List Ans) (hM : runB byType (dupT T R :: P0) m M = some L)
    (hL : allVal L = true) :
    answersB byType (dupT T R :: P0) (m + 6) (dupQ M) =
      some ((observe true L).map fun v => pairOf v v) := by
  rw [answersB_eq, dup_value hT hR hRc P0 hpair M m, runB_mono (by omega) hM]
  simp only [Option.map_some, Option.some.injEq]
  rw [observe_cont true _ L hL]
  simp only [observe]
  exact flatMap_single (fun v => pairOf v v) _

/-- With `M` printing the values `vs`, held text prints every pair. -/
theorem dup_held_printed {X R : CTy} (hX : X.holds = true) (hR : R.holds = false)
    (hRc : R.check = none) (P0 : TProg) (hpair : tmodesOf (dupT X R :: P0) "pair" 2 = none)
    (M : Atom) (m : Nat) (L : List Ans) (hM : runB byType (dupT X R :: P0) m M = some L)
    (hL : allVal L = true) :
    answersB byType (dupT X R :: P0) (m + 5) (dupQ M) =
      some ((observe true L).flatMap fun v => (observe true L).map fun w => pairOf v w) := by
  rw [answersB_eq, dup_held hX hR hRc P0 hpair M m L hM]
  simp only [Option.map_some, Option.some.injEq]
  have inner : ∀ v, observe true (cont (fun w => [(.val (pairOf v w), [])]) L) =
      (observe true L).map fun w => pairOf v w := by
    intro v
    rw [observe_cont true _ L hL]
    simp only [observe]
    exact flatMap_single (fun w => pairOf v w) _
  rw [Laws.observe_prefix, observe_cont true _ L hL]
  simp only [inner]

/-- **The duplication law as bags**: the value parameter's bag is the diagonal, held text's bag the
full product; they differ as soon as `M` has two different values. -/
theorem dup_bags {T X R : CTy} (hT : UncheckedT T) (hX : X.holds = true) (hR : R.holds = false)
    (hRc : R.check = none) (P0 : TProg) (hpT : tmodesOf (dupT T R :: P0) "pair" 2 = none)
    (hpX : tmodesOf (dupT X R :: P0) "pair" 2 = none) (M : Atom) (mT mX : Nat)
    (LT LX : List Ans) (hMT : runB byType (dupT T R :: P0) mT M = some LT)
    (hMX : runB byType (dupT X R :: P0) mX M = some LX) (hLT : allVal LT = true)
    (hLX : allVal LX = true) :
    ((answersB byType (dupT T R :: P0) (mT + 6) (dupQ M)).map fun l => (l : Multiset Atom)) =
        some (((observe true LT).map fun v => pairOf v v : List Atom) : Multiset Atom) ∧
      ((answersB byType (dupT X R :: P0) (mX + 5) (dupQ M)).map fun l => (l : Multiset Atom)) =
        some (((observe true LX).flatMap fun v => (observe true LX).map fun w => pairOf v w :
          List Atom) : Multiset Atom) := by
  rw [dup_value_printed hT hR hRc P0 hpT M mT LT hMT hLT,
    dup_held_printed hX hR hRc P0 hpX M mX LX hMX hLX]
  exact ⟨rfl, rfl⟩

/-! ## The control `(two)`, and the laws with alternatives -/

/-- `(dup (two))`: two equal pairs for a value parameter (`%Undefined%`, `Proc`), four pairs for
held text in `byType` (`Atom`, `(Code Number)`), `(pair (two) (two))` for `Atom` text in `codeOnly`
(the PeTTa lane's and the Prime draft's reading, as measured). -/
theorem dup_two_rows :
    answersB byType [dupT .undef .undef, twoT] F (dupQ (E [S "two"])) =
      some [pairOf (N 1) (N 1), pairOf (N 2) (N 2)] ∧
    answersB byType [dupT .proc .proc, twoT] F (dupQ (E [S "two"])) =
      some [pairOf (N 1) (N 1), pairOf (N 2) (N 2)] ∧
    answersB byType [dupT .atom .undef, twoT] F (dupQ (E [S "two"])) =
      some [pairOf (N 1) (N 1), pairOf (N 1) (N 2), pairOf (N 2) (N 1), pairOf (N 2) (N 2)] ∧
    answersB byType [dupT (.code .number) .undef, twoT] F (dupQ (E [S "two"])) =
      some [pairOf (N 1) (N 1), pairOf (N 1) (N 2), pairOf (N 2) (N 1), pairOf (N 2) (N 2)] ∧
    answersB codeOnly [dupT .atom .undef, twoT] F (dupQ (E [S "two"])) =
      some [pairOf (E [S "two"]) (E [S "two"])] := by
  decide +kernel

/-- The four laws with alternatives, on `(two)`: `let`, an evaluated identity, identity insertion
and weakening each keep the bag `1, 2`; the explicit hold keeps the text. -/
theorem laws_with_choice :
    answersB byType [twoT] F (Laws.letQ "y" (E [S "two"])) = some [N 1, N 2] ∧
    answersB byType [valueIdT .undef, twoT] F (Laws.idQ (E [S "two"])) = some [N 1, N 2] ∧
    answersB byType (identityProgT .atom .undef .undef [twoT]) F (Laws.gQ (E [S "two"])) =
      some [N 1, N 2] ∧
    answersB byType (identityProgT .atom .undef .undef [twoT]) F (Laws.g'Q (E [S "two"])) =
      some [N 1, N 2] ∧
    answersB byType [twoT, heldIdT "g" (.code .number) .number] F (E [S "g", E [S "two"]]) =
      some [N 1, N 2] ∧
    answersB byType [twoT, heldIdT "g" (.code .number) .undef] F (E [S "g", E [S "two"]]) =
      some [N 1, N 2] ∧
    answersB byType [twoT, holdFn, heldBodyT "g" .atom .undef (E [S "hold", V "x"])] F
      (E [S "g", E [S "two"]]) = some [E [S "two"]] := by
  decide +kernel

end ByType

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
