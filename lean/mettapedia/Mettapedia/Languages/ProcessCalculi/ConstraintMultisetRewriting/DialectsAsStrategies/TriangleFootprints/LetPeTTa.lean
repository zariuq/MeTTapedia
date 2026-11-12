import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.LetFrontier

/-!
# PeTTa's `let` with a variable pattern, and the value both dialects give

PeTTa's `let` is a special form: `(let p v b)` evaluates `v` under a binding frame, unifies `p` with
each answer and evaluates `b` under the extended bindings.

* `let_enter_step`, `binding_return_step`: the two transitions of PeTTa's streaming machine.
* `petta_let_root`: **from its entry, `(let $x d b)` with a data value `d` yields PeTTa's answers for
  the term `b` presents once its renamed `$x` is bound to `d`**, on any program. The statement is at
  the entry, where the renamed pattern variable is fresh: under bindings that already hold it, the
  binding frame clashes (`Controls.bound_clash`).
* `Controls.petta_five`: `(let $x 5 (pair $x $x))` yields `[(pair 5 5)]` from some fuel on, with no
  fuel bound on the proof; `Controls.petta_read_open`: `(let $x 5 $x)` yields `[5]`.
* `Controls.five_agree`: **HE and PeTTa give `(pair 5 5)`**: PeTTa's values, and the value every
  candidate frame of HE's `unify` publishes for the one work of every frontier of the call
  (`LetFrontier.Controls.five_semantics`).

## Controls

* `Controls.petta_five`, `Controls.petta_read_open`, `Controls.five_agree` (positive).
* `Controls.bound_clash` (negative): a binding frame whose pattern variable is already bound to `7`
  gives no continuation for the answer `5`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace LetPeTTa

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom applySubst)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables
open AnswerBags.Controls (sym app)
open LetFrontier (letRows)

section Steps

variable {registry : SpaceSemantics.Program}

/-- PeTTa enters `let`: the value is evaluated under the binding frame. -/
theorem let_enter_step (world : Streaming.World) (σ : Subst) (pattern value body : Atom)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Unifying.Answer)
    (next : Nat) :
    Streaming.Transition registry
      ⟨world, .execute ⟨.evaluate σ (.expression [.symbol "let", pattern, value, body]), frames⟩ ::
        older, answers, next⟩
      ⟨world, .execute ⟨.evaluate σ value, .source (.bind pattern body) :: frames⟩ :: older, answers,
        next⟩ :=
  .phase rfl rfl (.let_enter rfl) (.waiting rfl rfl)

/-- PeTTa's binding frame unifies the pattern with each answer and continues with the body. -/
theorem binding_return_step (world : Streaming.World) (answer : Unifying.Answer)
    (pattern body : Atom) {continued : List Unifying.Control}
    (bound : Unifying.bindAnswers pattern body [answer] = some continued)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Unifying.Answer)
    (next : Nat) :
    Streaming.Transition registry
      ⟨world, .execute ⟨.returned [answer], .source (.bind pattern body) :: frames⟩ :: older, answers,
        next⟩
      ⟨world, .execute ⟨.sequence continued [], frames⟩ :: older, answers, next⟩ :=
  .answer rfl (.source (.binding_return rfl rfl bound) (.plain rfl))

end Steps

/-- **PeTTa's `let` with a variable pattern, from its entry**: on any program, `(let $x d b)` with a
data value `d` binds the renamed `$x` to `d` (`bound`, a computation) and runs the renamed body,
which presents `t` under that binding; from some fuel on the values are PeTTa's answers for `t`. -/
theorem petta_let_root {atoms : List Atom} {x : String} {d : Atom} (data : DataAtom d) {b t : Atom}
    {L : List Atom} (clean : ∀ a ∈ L, Answerable a)
    (bound : Unifying.bindAnswers (.var (Unifying.freshName 0 x)) (Unifying.rename 0 b) [⟨d, []⟩] =
      some [.evaluate [(Unifying.freshName 0 x, d)] (Unifying.rename 0 b)])
    (body : PeTTaOpen atoms t L)
    (presented : Presents [(Unifying.freshName 0 x, d)] (Unifying.rename 0 b) t) :
    ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
      (Streaming.enter { state := store atoms } (.expression [.symbol "let", .var x, d, b]))) = L := by
  let σ' : Subst := [(Unifying.freshName 0 x, d)]
  let W : Streaming.World := { state := store atoms, uses := 1 }
  have ground : isGroundAtom d = true := (answerable_of_data data).ground
  have entered : Streaming.enter { state := store atoms } (.expression [.symbol "let", .var x, d, b]) =
      ⟨W, [.execute ⟨.evaluate [] (.expression [.symbol "let", .var (Unifying.freshName 0 x), d,
        Unifying.rename 0 b]), []⟩], [], 0⟩ := by
    simp only [Streaming.enter, Unifying.rename, Unifying.rename.renameList,
      Unifying.rename_ground 0 d ground, W]
  have renamed : Unifying.renameKeys 0 [(x, d)] ++ [] = σ' := rfl
  have fresh : ∀ k, Unifying.FreshFor (W.uses + k) σ' := by
    rw [← renamed]
    exact PeTTaRuns.freshFor_renamed (show 0 < 1 by decide) (fun _ _ => rfl)
  have range : Unifying.GroundRange σ' := by
    intro binding member
    simp only [σ', List.mem_cons, List.not_mem_nil, or_false] at member
    subst member
    exact ground
  obtain ⟨uses, out, _, valuesOut, path⟩ := body [] (fun v => [v])
    (fun v member => PeTTaRuns.delivers_root atoms (clean v member))
    W σ' rfl rfl range fresh (Unifying.rename 0 b) presented [] [] 0
  have full : PeTTaRuns.PSteps (translate atoms)
      ⟨W, [.execute ⟨.evaluate [] (.expression [.symbol "let", .var (Unifying.freshName 0 x), d,
        Unifying.rename 0 b]), []⟩], [], 0⟩
      ⟨{W with uses := uses}, [], [] ++ out, 0⟩ := by
    refine .head (let_enter_step W [] (.var (Unifying.freshName 0 x)) d (Unifying.rename 0 b)
      [] [] [] 0) ?_
    refine .head (PeTTaOpenRuns.evaluate_item W [] ⟨lit_of_data data, Or.inl rfl⟩ _ [] [] 0) ?_
    refine .head (binding_return_step W ⟨d, []⟩ (.var (Unifying.freshName 0 x)) (Unifying.rename 0 b)
      bound [] [] [] 0) ?_
    refine .head (PeTTaRuns.alternatives W _ [] [] [] 0) ?_
    exact path
  obtain ⟨N, reached⟩ := (Streaming.path_iff_advance _ _ _).mp full
  refine ⟨N, fun n bigger => ?_⟩
  rw [entered, show n = N + (n - N) by omega, Streaming.advance_add, reached, advance_finished]
  simpa [Streaming.values, flatMap_root] using valuesOut

/-! ## Controls -/

namespace Controls

open LetFrontier.Controls (fiveCall readCall)

theorem pair_ordinary : Ordinary WholeRunWords.Double.noHost letRows "pair"
    [.grounded (.int 5), .grounded (.int 5)] :=
  ⟨.symbol (by decide) (by decide), (fun a member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
      subst member
      exact .grounded _), (by decide +kernel), (fun impossible => impossible), (by decide),
    (by decide), (by decide), (by decide), (by decide), (by decide)⟩

theorem five_item : PresentsItem [("x#0", .grounded (.int 5))] (.var "x#0") (.grounded (.int 5)) :=
  ⟨.grounded _, Or.inr ⟨"x#0", rfl, rfl⟩⟩

/-- **PeTTa on `(let $x 5 (pair $x $x))`**: from some fuel on, the values are `[(pair 5 5)]`. -/
theorem petta_five : ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate letRows) n
    (Streaming.enter { state := store letRows } fiveCall)) =
      [app "pair" [.grounded (.int 5), .grounded (.int 5)]] :=
  petta_let_root (atoms := letRows) (x := "x") (.grounded (.int 5))
    (fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact app_answerable (.symbol (by decide) (by decide)) (fun a member => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
        subst member
        exact answerable_of_data (.grounded _)))
    rfl
    (petta_open_constructor pair_ordinary (by decide +kernel))
    (.call "pair" rfl (.cons five_item (.cons five_item .nil)))

/-- **PeTTa on `(let $x 5 $x)`**, through the same lemma: the values are `[5]` from some fuel on
(`LetFrontier.Controls.petta_read` checks fuel `6` directly). -/
theorem petta_read_open : ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate letRows) n
    (Streaming.enter { state := store letRows } readCall)) = [.grounded (.int 5)] :=
  petta_let_root (atoms := letRows) (x := "x") (.grounded (.int 5))
    (fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data (.grounded _))
    rfl (petta_open_data letRows (.grounded (.int 5))) (.item five_item)

/-- **Negative control**: under bindings that already hold the pattern variable at `7`, PeTTa's
binding frame gives the answer `5` no continuation; this is why `petta_let_root` is stated at the
entry, where the renamed variable is fresh. -/
theorem bound_clash : Unifying.bindAnswers (.var "x#0") (.var "x#0")
    [⟨.grounded (.int 5), [("x#0", .grounded (.int 7))]⟩] = some [] := rfl

/-- **HE and PeTTa give `(pair 5 5)` for `(let $x 5 (pair $x $x))`**: PeTTa's values from some fuel
on, and the value every candidate frame of HE's `unify` publishes for the one work of every frontier
of the call, at every frame of its bindings. -/
theorem five_agree (policy : Completed.Policy) (live : List Atom) :
    (∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate letRows) n
      (Streaming.enter { state := store letRows } fiveCall)) =
        [app "pair" [.grounded (.int 5), .grounded (.int 5)]]) ∧
    ∀ works, Steps.EquationFrontierRel (Mettapedia.Languages.MeTTa.HE.Space.ofList letRows) live
        fiveCall Mettapedia.Languages.MeTTa.HE.Bindings.empty works →
      ∃ (w : Steps.EquationWork) (rename : String → String), works = [w] ∧
        ∀ frame : Completed.Frame, frame.bindings = w.bindings →
          ∀ output : Completed.Frame, Steps.UnifyCandidateRel
              (frame.read policy (.var (rename "atom"))).erase
              (frame.read policy (.var (rename "pattern"))).erase frame.bindings output.bindings →
            (output.read policy (frame.read policy (.var (rename "template")))).erase =
              app "pair" [.grounded (.int 5), .grounded (.int 5)] :=
  ⟨petta_five, fun works frontier => LetFrontier.Controls.five_semantics policy live works frontier⟩

end Controls

#print axioms let_enter_step
#print axioms binding_return_step
#print axioms petta_let_root
#print axioms Controls.petta_five
#print axioms Controls.petta_read_open
#print axioms Controls.bound_clash
#print axioms Controls.five_agree

end LetPeTTa

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
