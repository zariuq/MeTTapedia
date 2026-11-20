import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Weakening

/-!
# The laws, design by design

A query **prints** `L` (`Prints`) when some fuel finishes its run with the printed answers `L`; by
`CoreLaws.exec_det` a query prints at most one list (`Prints.det`).

| law | statement |
|---|---|
| `KeepsWeakening` | a weaker result type changes no answer (module `Weakening`) |
| `KeepsLet` | `(let $y M $y)` prints what `M` prints |
| `KeepsValuesFinal` | through an evaluated identity, `(myid M)` prints what `M` prints |
| `KeepsPlainReading` | `(= (g $x) $x)`, `$x` held, result `Proc`/`%Undefined%`/`$t`: `(g M)` prints what `M` prints |
| `KeepsIf` | `(my-if True M N)`, HE's `if` as a function: prints what `M` prints |
| `KeepsIdentity` | `(= (g $x) $x)` and `(= (g' $x) (myid $x))` print alike |
| `KeepsAtomCode` | `(: g (-> Atom Atom)) (= (g $x) B)`: `(g M)` prints `B` with `M` for `$x`, as written |
| `KeepsSubstitution` | `(let $y M B)` prints what `B` with `M`'s printed value for `$y` prints |

General theorems: `keepsLet_of` and `keepsValuesFinal_of` (every design where values are final),
`keepsPlainReading_of` and `keepsIf_of` (every design where a held parameter runs at the root under
those result types), `keepsIdentity_of` (values final, and a held parameter runs at the root exactly
when it runs inside), `keepsAtomCode_of` (every design returning `Atom` bodies as written). They
rest on exact computations of the elaborated core (`runQ_let`, `runQ_myid`, `runQ_heldId`,
`runQ_myIf`, `runQ_viaId`, `runQ_atomFn`) in which the user's terms are arbitrary.
Refutations are smallest programs run by the kernel (`he_breaks_let`, ...).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core CoreLaws Acceptance Weakening

namespace Laws

/-! ## Printing -/

/-- The query prints `L` with some fuel. -/
def Prints (D : Design) (P : SProg) (q : Atom) (L : List Atom) : Prop :=
  ∃ n, answers D P n q = some L

theorem answers_eq (D : Design) (P : SProg) (n : Nat) (q : Atom) :
    answers D P n q = (runQ D P n q).map (observe D.reportsRefusal) := rfl

theorem runQ_mono {D : Design} {P : SProg} {q : Atom} {n m : Nat} (le : n ≤ m) {A : List Ans}
    (h : runQ D P n q = some A) : runQ D P m q = some A :=
  exec_mono _ le _ _ h

/-- A query prints at most one list. -/
theorem Prints.det {D : Design} {P : SProg} {q : Atom} {L L' : List Atom}
    (h : Prints D P q L) (h' : Prints D P q L') : L = L' := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := h'
  rw [answers_eq] at hn hm
  cases hA : runQ D P n q with
  | none => rw [hA] at hn; exact absurd hn (by simp)
  | some A =>
      cases hB : runQ D P m q with
      | none => rw [hB] at hm; exact absurd hm (by simp)
      | some B =>
          rw [hA] at hn
          rw [hB] at hm
          have := exec_det (elabProg D P) _ hA hB
          subst this
          exact (Option.some.inj hn).symm.trans (Option.some.inj hm)

/-- Two queries print alike when their runs agree, up to the observation, at a fixed difference of
fuel. -/
theorem prints_iff_of_shift {D : Design} {P : SProg} {q q' : Atom} (a b : Nat)
    (shift : ∀ n, (runQ D P (n + a) q).map (observe D.reportsRefusal) =
      (runQ D P (n + b) q').map (observe D.reportsRefusal))
    (L : List Atom) : Prints D P q L ↔ Prints D P q' L := by
  constructor
  · rintro ⟨n, hn⟩
    rw [answers_eq] at hn
    cases hA : runQ D P n q with
    | none => rw [hA] at hn; exact absurd hn (by simp)
    | some A =>
        rw [hA] at hn
        refine ⟨n + b, ?_⟩
        rw [answers_eq, ← shift n, runQ_mono (by omega) hA]
        exact hn
  · rintro ⟨n, hn⟩
    rw [answers_eq] at hn
    cases hA : runQ D P n q' with
    | none => rw [hA] at hn; exact absurd hn (by simp)
    | some A =>
        rw [hA] at hn
        refine ⟨n + a, ?_⟩
        rw [answers_eq, shift n, runQ_mono (by omega) hA]
        exact hn

/-- Two queries that print different lists do not print alike. -/
theorem not_iff_of_prints {D D' : Design} {P P' : SProg} {q q' : Atom} {L L' : List Atom}
    (h : Prints D P q L) (h' : Prints D' P' q' L') (ne : L ≠ L') :
    ¬ (Prints D P q L' ↔ Prints D' P' q' L') :=
  fun iff => ne (Prints.det h (iff.mpr h'))

/-! ## Unfolding lemmas -/

/-- Prefix a head to an answer's trace. -/
def prefixTrace (f : String) (a : Ans) : Ans := (a.1, f :: a.2)

theorem observe_prefix (b : Bool) (f : String) (L : List Ans) :
    observe b (L.map (prefixTrace f)) = observe b L := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
      obtain ⟨o, tr⟩ := a
      cases o with
      | val v => simp [observe, prefixTrace, ih]
      | refused d k => cases b <;> simp [observe, prefixTrace, ih]

theorem exec_enter (P : Prog) (n : Nat) (f : String) (args : List Atom) :
    exec P (n + 1) (.enter f args) =
      match P.find f args.length with
      | none => some [(.val (.expression (.symbol f :: args)), [])]
      | some d =>
          match firstRefusal d.argChecks args with
          | some (a, k) => some [(.refused a k, [f])]
          | none =>
              if anyClauseMatches args d.clauses then
                (runClauses (fun ρ c => exec P n (.comp ρ c)) args d.clauses).map
                  (List.map fun a => (checkResult d.resultCheck a.1, f :: a.2))
              else some [(.val (.expression (.symbol f :: args)), [f])] := rfl

/-- Entering a definition whose first clause matches the arguments and whose other clauses do not,
with no result check. -/
theorem exec_enter_first (Q : Prog) (f : String) (args : List Atom) (d : Def)
    (pats : List Atom) (body : Comp) (rest : List (List Atom × Comp)) (ρ : Env) (k : Nat)
    (hfind : Q.find f args.length = some d) (hargs : firstRefusal d.argChecks args = none)
    (hres : d.resultCheck = none) (hcl : d.clauses = (pats, body) :: rest)
    (hm : matchAtom.matchList pats args [] = some ρ)
    (hrest : ∀ ev, runClauses ev args rest = some []) :
    exec Q (k + 1) (.enter f args) =
      (exec Q k (.comp ρ body)).map (List.map (prefixTrace f)) := by
  rw [exec_enter, hfind]
  simp only
  rw [hargs]
  simp only
  have hany : anyClauseMatches args d.clauses = true := by
    rw [hcl]; simp [anyClauseMatches, hm]
  rw [if_pos hany, hcl]
  have hrun : runClauses (fun ρ c => exec Q k (.comp ρ c)) args ((pats, body) :: rest) =
      (exec Q k (.comp ρ body)).map (· ++ []) := by
    simp only [runClauses, hm, hrest]
  rw [hrun, hres]
  cases exec Q k (.comp ρ body) with
  | none => rfl
  | some L => simp [prefixTrace, checkResult]

theorem continueEach_one (k : Atom → Option (List Ans)) (v : Atom) :
    continueEach k [(.val v, [])] = k v := by
  unfold continueEach
  cases k v with
  | none => rfl
  | some here => simp [continueEach]

/-- Binding a returned template: the rest runs with the instance bound, one step later. -/
theorem exec_bind_ret_val (P : Prog) (n : Nat) (ρ : Env) (t : Atom) (x : String) (k : Comp) :
    exec P (n + 2) (.comp ρ (.bind (.ret t) x k)) =
      exec P (n + 1) (.comp ((x, inst ρ t) :: ρ) k) := by
  rw [exec_bind, exec_ret]
  simp only [Option.bind_some]
  exact continueEach_one _ _

/-- An occurrence of a held variable runs or is passed, as the body's rule says. -/
theorem elabVar_held (D : Design) {held : List String} (heldRun : Bool → Bool) (isRoot : Bool)
    {x : String} (hx : held.contains x = true) :
    elabVar D held heldRun isRoot x =
      if heldRun isRoot then .run (.var x) else .ret (.var x) := by
  unfold elabVar
  rw [if_pos hx]

/-! ## `let` -/

/-- `(let $y M $y)`. -/
def letQ (y : String) (M : Atom) : Atom := E [S "let", V y, M, V y]

theorem elabQuery_let (D : Design) (ms : Modes) (y : String) (M : Atom) :
    elabQuery D ms (letQ y M) =
      .bind (elabQuery D ms M) y (elabVar D [] (fun _ => false) false y) := rfl

/-- Where values are final, `(let $y M $y)` is `M`, one step later. -/
theorem runQ_let (D : Design) (hr : D.rerunValues = false) (P : SProg) (y : String)
    (M : Atom) (n : Nat) : runQ D P (n + 2) (letQ y M) = runQ D P (n + 1) M := by
  unfold runQ
  rw [elabQuery_let]
  have hv : elabVar D [] (fun _ => false) false y = .ret (.var y) := by
    simp [elabVar, hr]
  rw [hv]
  exact exec_bind_ret _ _ _ _ _

/-- **The `let` law.** -/
def KeepsLet (D : Design) : Prop :=
  ∀ (P : SProg) (y : String) (M : Atom) (L : List Atom), Prints D P (letQ y M) L ↔ Prints D P M L

theorem keepsLet_of (D : Design) (hr : D.rerunValues = false) : KeepsLet D := by
  intro P y M L
  apply prints_iff_of_shift 2 1
  intro n
  rw [runQ_let D hr]

/-- Hyperon Experimental breaks the `let` law: `(let $y (held-atom (f a)) $y)` prints `5`, while
`(held-atom (f a))` prints `(f a)`. -/
theorem he_breaks_let : ¬ KeepsLet he := by
  intro h
  have hlet : Prints he letProg qLet [N 5] := ⟨F, by decide +kernel⟩
  have hM : Prints he letProg (E [S "held-atom", callFA]) [callFA] := ⟨F, by decide +kernel⟩
  exact not_iff_of_prints hlet hM (by decide) (h letProg "y" (E [S "held-atom", callFA]) [callFA])

/-! ## Values are final -/

/-- `(myid M)`. -/
def idQ (M : Atom) : Atom := E [S "myid", M]

/-- The computation types whose parameters run without a check. -/
def Unchecked (T : Ty) : Prop := T = .proc ∨ T = .undef ∨ T = .tvar

theorem runQ_myid (D : Design) (hr : D.rerunValues = false) (T : Ty) (hT : Unchecked T)
    (P0 : SProg) (M : Atom) (m : Nat) :
    runQ D (valueId "myid" T :: P0) (m + 4) (idQ M) =
      (runQ D (valueId "myid" T :: P0) (m + 3) M).map fun L =>
        L.map fun a => match a with
          | (.val v, trace) => (.val v, trace ++ ["myid"])
          | (.refused d k, trace) => (.refused d k, trace) := by
  obtain ⟨held, p, r, a, c, rep⟩ := D
  simp only at hr
  subst hr
  have hq : elabQuery ⟨held, p, false, a, c, rep⟩ (modesOf (valueId "myid" T :: P0)) (idQ M) =
      .bind (elabQuery ⟨held, p, false, a, c, rep⟩ (modesOf (valueId "myid" T :: P0)) M)
        (slot 0) (.call "myid" [.var (slot 0)]) := by
    rcases hT with rfl | rfl | rfl <;> rfl
  have hk : (fun v => exec (elabProg ⟨held, p, false, a, c, rep⟩ (valueId "myid" T :: P0))
      (m + 3) (.comp [(slot 0, v)] (.call "myid" [.var (slot 0)]))) =
      fun v => some [(.val v, ["myid"])] := by
    funext v
    rw [exec_call]
    simp only [List.map, inst_var_head]
    rcases hT with rfl | rfl | rfl <;>
    · rw [exec_enter_first _ "myid" [v] _ [.var "x"] (.ret (.var "x")) [] [("x", v)] (m + 1) rfl
        rfl rfl rfl rfl fun _ => rfl]
      rfl
  unfold runQ
  rw [hq, exec_bind, hk]
  cases exec _ (m + 3) _ with
  | none => rfl
  | some L => exact continueEach_single L "myid"

/-- **Values are final.** -/
def KeepsValuesFinal (D : Design) : Prop :=
  ∀ (P0 : SProg) (T : Ty) (M : Atom) (L : List Atom), Unchecked T →
    (Prints D (valueId "myid" T :: P0) (idQ M) L ↔ Prints D (valueId "myid" T :: P0) M L)

theorem keepsValuesFinal_of (D : Design) (hr : D.rerunValues = false) : KeepsValuesFinal D := by
  intro P0 T M L hT
  apply prints_iff_of_shift 4 3
  intro n
  rw [runQ_myid D hr T hT P0 M n]
  cases runQ D (valueId "myid" T :: P0) (n + 3) M with
  | none => rfl
  | some A => simp only [Option.map_some]; congr 1; exact observe_appendTrace _ A "myid"

/-- Hyperon Experimental breaks it: `(compute (held-atom (f a)))` prints `5`, the argument
`(held-atom (f a))` prints `(f a)` (measured row 5). -/
theorem he_breaks_valuesFinal : ¬ KeepsValuesFinal he := by
  intro h
  have hid : Prints he (valueId "myid" .undef :: letProg) (idQ (E [S "held-atom", callFA])) [N 5] :=
    ⟨F, by decide +kernel⟩
  have hM : Prints he (valueId "myid" .undef :: letProg) (E [S "held-atom", callFA]) [callFA] :=
    ⟨F, by decide +kernel⟩
  exact not_iff_of_prints hid hM (by decide)
    (h letProg .undef (E [S "held-atom", callFA]) [callFA] (.inr (.inl rfl)))

/-! ## The equation's plain reading, at the root -/

/-- `(g M)`. -/
def gQ (M : Atom) : Atom := E [S "g", M]

theorem body_heldVar (D : Design) (ms : Modes) (R : Ty) (hR : Unchecked R) (held : List String)
    (x : String) (hx : held.contains x = true) :
    elabBody D ms held R (.var x) =
      if heldRunsAt D (D.heldUnder R) true then .run (.var x) else .ret (.var x) := by
  have hb : elabBody D ms held R (.var x) =
      elabVar D held (heldRunsAt D (D.heldUnder R)) true x := by
    rcases hR with rfl | rfl | rfl <;> rfl
  rw [hb, elabVar_held D _ true hx]

theorem runQ_heldId (D : Design) (R : Ty) (hR : Unchecked R) (P0 : SProg) (M : Atom) (m : Nat) :
    runQ D (heldId "g" R :: P0) (m + 4) (gQ M) =
      if heldRunsAt D (D.heldUnder R) true then
        (runQ D (heldId "g" R :: P0) (m + 1) M).map (List.map (prefixTrace "g"))
      else some [(.val M, ["g"])] := by
  have hbody := body_heldVar D (modesOf (heldId "g" R :: P0)) R hR ["x"] "x" rfl
  have hq : elabQuery D (modesOf (heldId "g" R :: P0)) (gQ M) = .call "g" [M] := rfl
  have hcl : (elabFn D (modesOf (heldId "g" R :: P0)) (heldId "g" R)).clauses =
      [([.var "x"], if heldRunsAt D (D.heldUnder R) true then .run (.var "x")
        else .ret (.var "x"))] := by
    show [([Atom.var "x"], elabBody D (modesOf (heldId "g" R :: P0))
      (heldVars [.atom] [Atom.var "x"]) R (Atom.var "x"))] = _
    rw [show heldVars [.atom] [Atom.var "x"] = ["x"] from rfl, hbody]
  have hres : (elabFn D (modesOf (heldId "g" R :: P0)) (heldId "g" R)).resultCheck = none := by
    rcases hR with rfl | rfl | rfl <;> rfl
  unfold runQ
  rw [hq, exec_call]
  simp only [List.map, inst_nil]
  rw [exec_enter_first _ "g" [M] _ [.var "x"] _ [] [("x", M)] (m + 2) rfl rfl hres hcl rfl
    fun _ => rfl]
  by_cases hc : heldRunsAt D (D.heldUnder R) true
  · rw [if_pos hc, if_pos hc, exec_run, inst_var_head]
    rfl
  · rw [if_neg hc, if_neg hc]
    rfl

/-- **The equation's plain reading at the root**: a held parameter returned as the whole body. -/
def KeepsPlainReading (D : Design) : Prop :=
  ∀ (P0 : SProg) (R : Ty) (M : Atom) (L : List Atom), Unchecked R →
    (Prints D (heldId "g" R :: P0) (gQ M) L ↔ Prints D (heldId "g" R :: P0) M L)

theorem keepsPlainReading_of (D : Design)
    (h : ∀ R, Unchecked R → heldRunsAt D (D.heldUnder R) true = true) : KeepsPlainReading D := by
  intro P0 R M L hR
  apply prints_iff_of_shift 4 1
  intro n
  rw [runQ_heldId D R hR P0 M n, if_pos (h R hR)]
  cases runQ D (heldId "g" R :: P0) (n + 1) M with
  | none => rfl
  | some A => simp only [Option.map_some]; congr 1; exact observe_prefix _ "g" A

/-- Code value breaks it: `(g (f a))` prints `(f a)`, `(f a)` prints `5`. -/
theorem codeValue_breaks_plainReading : ¬ KeepsPlainReading codeValue := by
  intro h
  have hg : Prints codeValue (heldId "g" .undef :: [fA]) (gQ callFA) [callFA] :=
    ⟨F, by decide +kernel⟩
  have hM : Prints codeValue (heldId "g" .undef :: [fA]) callFA [N 5] := ⟨F, by decide +kernel⟩
  exact not_iff_of_prints hg hM (by decide) (h [fA] .undef callFA [N 5] (.inr (.inl rfl)))

/-! ## HE's `if` written as a function -/

/-- `(my-if True M N)`. -/
def ifQ (M N : Atom) : Atom := E [S "my-if", S "True", M, N]

/-- No variable occurs in the term. -/
def Closed (t : Atom) : Prop := patVars t = []

theorem runQ_myIf (D : Design) (R : Ty) (hR : Unchecked R) (P0 : SProg) (M N : Atom)
    (hM : Closed M) (hN : Closed N) (m : Nat) :
    runQ D (myIf R :: P0) (m + 5) (ifQ M N) =
      if heldRunsAt D (D.heldUnder R) true then
        (runQ D (myIf R :: P0) (m + 1) M).map (List.map (prefixTrace "my-if"))
      else some [(.val M, ["my-if"])] := by
  have hbody := body_heldVar D (modesOf (myIf R :: P0)) R hR ["t", "e"] "t" rfl
  have hq : elabQuery D (modesOf (myIf R :: P0)) (ifQ M N) =
      .bind (.ret (S "True")) (slot 0) (.call "my-if" [.var (slot 0), M, N]) := rfl
  have hcl : (elabFn D (modesOf (myIf R :: P0)) (myIf R)).clauses =
      ([.symbol "True", .var "t", .var "e"], if heldRunsAt D (D.heldUnder R) true then
        .run (.var "t") else .ret (.var "t")) ::
      [([.symbol "False", .var "t", .var "e"],
        elabBody D (modesOf (myIf R :: P0)) ["t", "e"] R (.var "e"))] := by
    show [([Atom.symbol "True", Atom.var "t", Atom.var "e"], elabBody D (modesOf (myIf R :: P0))
        (heldVars [.bool, .atom, .atom] [Atom.symbol "True", Atom.var "t", Atom.var "e"]) R
          (Atom.var "t")),
      ([Atom.symbol "False", Atom.var "t", Atom.var "e"], elabBody D (modesOf (myIf R :: P0))
        (heldVars [.bool, .atom, .atom] [Atom.symbol "False", Atom.var "t", Atom.var "e"]) R
          (Atom.var "e"))] = _
    rw [show heldVars [.bool, .atom, .atom] [Atom.symbol "True", Atom.var "t", Atom.var "e"] =
        ["t", "e"] from rfl,
      show heldVars [.bool, .atom, .atom] [Atom.symbol "False", Atom.var "t", Atom.var "e"] =
        ["t", "e"] from rfl, hbody]
  have hres : (elabFn D (modesOf (myIf R :: P0)) (myIf R)).resultCheck = none := by
    rcases hR with rfl | rfl | rfl <;> rfl
  unfold runQ
  rw [hq, exec_bind_ret_val, exec_call]
  simp only [List.map, inst_var_head, inst_nil, inst_closed _ M hM, inst_closed _ N hN]
  rw [exec_enter_first _ "my-if" [S "True", M, N] _ [.symbol "True", .var "t", .var "e"] _ _
    [("e", N), ("t", M)] (m + 2) rfl rfl hres hcl rfl fun _ => rfl]
  by_cases hc : heldRunsAt D (D.heldUnder R) true
  · rw [if_pos hc, if_pos hc, exec_run]
    rfl
  · rw [if_neg hc, if_neg hc]
    rfl

/-- **HE's `if`** selects and runs exactly one branch: `(my-if True M N)` prints what `M` prints,
for all closed `M` and `N`. -/
def KeepsIf (D : Design) : Prop :=
  ∀ (P0 : SProg) (R : Ty) (M N : Atom) (L : List Atom), Unchecked R → Closed M → Closed N →
    (Prints D (myIf R :: P0) (ifQ M N) L ↔ Prints D (myIf R :: P0) M L)

theorem keepsIf_of (D : Design)
    (h : ∀ R, Unchecked R → heldRunsAt D (D.heldUnder R) true = true) : KeepsIf D := by
  intro P0 R M N L hR hM hN
  apply prints_iff_of_shift 5 1
  intro n
  rw [runQ_myIf D R hR P0 M N hM hN n, if_pos (h R hR)]
  cases runQ D (myIf R :: P0) (n + 1) M with
  | none => rfl
  | some A => simp only [Option.map_some]; congr 1; exact observe_prefix _ "my-if" A

/-- Code value selects the branch and returns it as written: `(my-if True (f a) (boom))` prints
`(f a)` (measured row 8, PeTTa). -/
theorem codeValue_breaks_if : ¬ KeepsIf codeValue := by
  intro h
  have hif : Prints codeValue (myIf .undef :: [fA]) (ifQ callFA (E [S "boom"])) [callFA] :=
    ⟨F, by decide +kernel⟩
  have hM : Prints codeValue (myIf .undef :: [fA]) callFA [N 5] := ⟨F, by decide +kernel⟩
  exact not_iff_of_prints hif hM (by decide)
    (h [fA] .undef callFA (E [S "boom"]) [N 5] (.inr (.inl rfl)) rfl rfl)

/-- The branch left alone is never run: whatever `N` is, the answer is `M`'s (the two `N` below,
a call with no equation and a call of `f`, give the same answer). -/
theorem if_other_branch_irrelevant :
    answers byName (myIf .undef :: [fA]) F (ifQ callFA (E [S "boom"])) = some [N 5] ∧
    answers byName (myIf .undef :: [fA]) F (ifQ callFA callFA) = some [N 5] := by
  decide +kernel

/-! ## Identity insertion -/

/-- `(: g' (-> Atom R)) (= (g' $x) (myid $x))`. -/
def viaIdFn (R : Ty) : Fn := ⟨"g'", some ([.atom], R), [([V "x"], E [S "myid", V "x"])]⟩

/-- The program of the identity law. -/
def identityProg (R T : Ty) (P0 : SProg) : SProg :=
  heldId "g" R :: viaIdFn R :: valueId "myid" T :: P0

/-- `(g' M)`. -/
def g'Q (M : Atom) : Atom := E [S "g'", M]

theorem runQ_viaId (D : Design) (hr : D.rerunValues = false) (R T : Ty) (hR : Unchecked R)
    (hT : Unchecked T) (P0 : SProg) (M : Atom) (m : Nat) :
    (runQ D (identityProg R T P0) (m + 6) (g'Q M)).map (observe D.reportsRefusal) =
      if heldRunsAt D (D.heldUnder R) false then
        (runQ D (identityProg R T P0) (m + 2) M).map (observe D.reportsRefusal)
      else some (observe D.reportsRefusal [(.val M, ["g'", "myid"])]) := by
  obtain ⟨held, p, r, a, c, rep⟩ := D
  simp only at hr
  subst hr
  have hq : elabQuery ⟨held, p, false, a, c, rep⟩ (modesOf (identityProg R T P0)) (g'Q M) =
      .call "g'" [M] := rfl
  have hcl : (elabFn ⟨held, p, false, a, c, rep⟩ (modesOf (identityProg R T P0)) (viaIdFn R)).clauses =
      [([.var "x"], .bind (if heldRunsAt ⟨held, p, false, a, c, rep⟩
          (Design.heldUnder ⟨held, p, false, a, c, rep⟩ R) false then .run (.var "x")
          else .ret (.var "x")) (slot 0) (.call "myid" [.var (slot 0)]))] := by
    rcases hR with rfl | rfl | rfl <;> rcases hT with rfl | rfl | rfl <;> rfl
  have hres : (elabFn ⟨held, p, false, a, c, rep⟩ (modesOf (identityProg R T P0))
      (viaIdFn R)).resultCheck = none := by
    rcases hR with rfl | rfl | rfl <;> rfl
  have hk : ∀ v, exec (elabProg ⟨held, p, false, a, c, rep⟩ (identityProg R T P0)) (m + 3)
      (.comp ((slot 0, v) :: [("x", M)]) (.call "myid" [.var (slot 0)])) =
        some [(.val v, ["myid"])] := by
    intro v
    rw [exec_call]
    simp only [List.map, inst_var_head]
    rcases hT with rfl | rfl | rfl <;>
    · rw [exec_enter_first _ "myid" [v] _ [.var "x"] (.ret (.var "x")) [] [("x", v)] (m + 1)
        rfl rfl rfl rfl rfl fun _ => rfl]
      rfl
  unfold runQ
  rw [hq, exec_call]
  simp only [List.map, inst_nil]
  rw [exec_enter_first _ "g'" [M] _ [.var "x"] _ [] [("x", M)] (m + 4) rfl rfl hres hcl rfl
    fun _ => rfl]
  by_cases hc : heldRunsAt ⟨held, p, false, a, c, rep⟩
      (Design.heldUnder ⟨held, p, false, a, c, rep⟩ R) false
  · rw [if_pos hc, if_pos hc, exec_bind, exec_run, inst_var_head]
    simp only [hk]
    rw [show (elabProg ⟨held, p, false, a, c, rep⟩ (identityProg R T P0)).code M =
      elabQuery ⟨held, p, false, a, c, rep⟩ (modesOf (identityProg R T P0)) M from rfl]
    cases exec (elabProg ⟨held, p, false, a, c, rep⟩ (identityProg R T P0)) (m + 2)
        (.comp [] (elabQuery ⟨held, p, false, a, c, rep⟩ (modesOf (identityProg R T P0)) M)) with
    | none => rfl
    | some L =>
        simp only [Option.bind_some, Option.map_some, continueEach_single]
        congr 1
        rw [observe_prefix, observe_appendTrace]
  · rw [if_neg hc, if_neg hc, exec_bind_ret_val, hk]
    simp only [inst_var_head, Option.map_some, List.map, prefixTrace]

/-- **Identity insertion**: passing a held parameter through an evaluated identity before returning
it changes no answer. -/
def KeepsIdentity (D : Design) : Prop :=
  ∀ (P0 : SProg) (R T : Ty) (M : Atom) (L : List Atom), Unchecked R → Unchecked T →
    (Prints D (identityProg R T P0) (gQ M) L ↔ Prints D (identityProg R T P0) (g'Q M) L)

theorem keepsIdentity_of (D : Design) (hr : D.rerunValues = false)
    (h : ∀ R, Unchecked R → heldRunsAt D (D.heldUnder R) true =
      heldRunsAt D (D.heldUnder R) false) : KeepsIdentity D := by
  intro P0 R T M L hR hT
  apply prints_iff_of_shift 5 6
  intro n
  rw [runQ_viaId D hr R T hR hT P0 M n, ← h R hR]
  change (runQ D (heldId "g" R :: viaIdFn R :: valueId "myid" T :: P0) (n + 1 + 4) (gQ M)).map
    (observe D.reportsRefusal) = _
  rw [runQ_heldId D R hR (viaIdFn R :: valueId "myid" T :: P0) M (n + 1)]
  by_cases hc : heldRunsAt D (D.heldUnder R) true
  · rw [if_pos hc, if_pos hc]
    change ((runQ D (heldId "g" R :: viaIdFn R :: valueId "myid" T :: P0) (n + 1 + 1) M).map
        (List.map (prefixTrace "g"))).map (observe D.reportsRefusal) =
      (runQ D (heldId "g" R :: viaIdFn R :: valueId "myid" T :: P0) (n + 1 + 1) M).map
        (observe D.reportsRefusal)
    cases runQ D (heldId "g" R :: viaIdFn R :: valueId "myid" T :: P0) (n + 1 + 1) M with
    | none => rfl
    | some A => simp only [Option.map_some]; congr 1; exact observe_prefix _ "g" A
  · rw [if_neg hc, if_neg hc]
    simp only [Option.map_some, observe]

/-- The Prime draft breaks identity insertion: `(g (f a))` prints `5`, `(g' (f a))` prints `(f a)`
(measured: `via-id` answers `(f a)`). -/
theorem primeToday_breaks_identity : ¬ KeepsIdentity primeToday := by
  intro h
  have hg : Prints primeToday (identityProg .undef .undef [fA]) (gQ callFA) [N 5] :=
    ⟨F, by decide +kernel⟩
  have hg' : Prints primeToday (identityProg .undef .undef [fA]) (g'Q callFA) [callFA] :=
    ⟨F, by decide +kernel⟩
  exact not_iff_of_prints hg hg' (by decide)
    (h [fA] .undef .undef callFA [callFA] (.inr (.inl rfl)) (.inr (.inl rfl)))

/-- Hyperon Experimental breaks it on a held code-returning call: `(g (held-atom (f a)))` prints
`(f a)`, `(g' (held-atom (f a)))` prints `5` (the evaluated identity runs the value again). -/
theorem he_breaks_identity : ¬ KeepsIdentity he := by
  intro h
  have hg : Prints he (identityProg .undef .undef letProg) (gQ (E [S "held-atom", callFA]))
      [callFA] := ⟨F, by decide +kernel⟩
  have hg' : Prints he (identityProg .undef .undef letProg) (g'Q (E [S "held-atom", callFA]))
      [N 5] := ⟨F, by decide +kernel⟩
  exact not_iff_of_prints hg hg' (by decide)
    (h letProg .undef .undef (E [S "held-atom", callFA]) [N 5] (.inr (.inl rfl)) (.inr (.inl rfl)))

/-! ## `Atom` as a result type -/

/-- `(: g (-> Atom Atom)) (= (g $x) B)`. -/
def atomFn (B : Atom) : Fn := ⟨"g", some ([.atom], .atom), [([V "x"], B)]⟩

theorem runQ_atomFn (D : Design) (ha : D.atomBody = false) (B : Atom) (P0 : SProg) (M : Atom) :
    runQ D (atomFn B :: P0) 3 (gQ M) = some [(.val (inst [("x", M)] B), ["g"])] := by
  obtain ⟨held, p, r, a, c, rep⟩ := D
  simp only at ha
  subst ha
  unfold runQ
  rw [show elabQuery ⟨held, p, r, false, c, rep⟩ (modesOf (atomFn B :: P0)) (gQ M) =
      .call "g" [M] from rfl, exec_call]
  simp only [List.map, inst_nil]
  rw [exec_enter_first _ "g" [M] _ [.var "x"] (.ret B) [] [("x", M)] 1 rfl rfl rfl rfl rfl
    fun _ => rfl]
  rfl

/-- **An `Atom` result builds code**: the body comes back as written, with the argument's text for
the parameter; nothing it builds is run. -/
def KeepsAtomCode (D : Design) : Prop :=
  ∀ (P0 : SProg) (B M : Atom), Prints D (atomFn B :: P0) (gQ M) [inst [("x", M)] B]

theorem keepsAtomCode_of (D : Design) (ha : D.atomBody = false) : KeepsAtomCode D := by
  intro P0 B M
  refine ⟨3, ?_⟩
  rw [answers_eq, runQ_atomFn D ha B P0 M]
  rfl

/-- The Prime draft breaks it: `(= (g $x) (+ 1 2))` under `Atom` prints `3`. -/
theorem primeToday_breaks_atomCode : ¬ KeepsAtomCode primeToday := by
  intro h
  have h1 := h [] (E [S "+", N 1, N 2]) (N 0)
  have h2 : Prints primeToday [atomFn (E [S "+", N 1, N 2])] (gQ (N 0)) [N 3] :=
    ⟨F, by decide +kernel⟩
  exact absurd (Prints.det h1 h2) (by decide +kernel)

/-- The law the Prime draft's choice keeps instead, on the measured rows 7: declaring the result
`Atom` or `%Undefined%` gives the same answer for a body without held parameters,
`(pair 3 4)` both; in the designs that return `Atom` bodies as written the two differ. -/
def mk2Prog : SProg :=
  [⟨"mk", some ([.number], .undef), [([V "n"], E [S "pair", V "n", E [S "+", V "n", N 1]])]⟩]

theorem atom_result_neutral_rows :
    answers primeToday mkProg F qMk = answers primeToday mk2Prog F qMk ∧
    answers hybrid mkProg F qMk = answers hybrid mk2Prog F qMk ∧
    answers he mkProg F qMk ≠ answers he mk2Prog F qMk ∧
    answers byName mkProg F qMk ≠ answers byName mk2Prog F qMk ∧
    answers codeValue mkProg F qMk ≠ answers codeValue mk2Prog F qMk := by
  decide +kernel

/-- With no held variable in scope, the held rule is never consulted. -/
theorem elabC_heldRun_irrelevant (D : Design) (ms : Modes) (hr hr' : Bool → Bool)
    (held : List String) (isRoot : Bool) (t : Atom) (hh : held = []) :
    elabC D ms held hr isRoot t = elabC D ms held hr' isRoot t := by
  revert hh
  refine elabC.induct D ms
    (motive_1 := fun held isRoot t => held = [] →
      elabC D ms held hr isRoot t = elabC D ms held hr' isRoot t)
    (motive_2 := fun held ps args i acc k => held = [] →
      elabArgs D ms held hr ps args i acc k = elabArgs D ms held hr' ps args i acc k)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ held isRoot t
  · intro held isRoot x h; subst h; simp [elabC, elabVar]
  · intro held isRoot y src body ihs ihb h; subst h
    rw [elabC.eq_2, elabC.eq_2, ihs rfl, ihb (by simp)]
  · intro held isRoot m ih h; subst h
    rw [elabC.eq_3, elabC.eq_3, ih rfl]
  · intro held isRoot a b iha ihb h; subst h
    rw [elabC.eq_4, elabC.eq_4, iha rfl, ihb rfl]
  · intro held isRoot h args hl he hp ps hms ih hh; subst hh
    rw [elabC.eq_5 _ _ _ _ _ _ _ hl he hp, elabC.eq_5 _ _ _ _ _ _ _ hl he hp, hms]
    exact ih rfl
  · intro held isRoot h args hl he hp hms hc ih hh; subst hh
    rw [elabC.eq_5 _ _ _ _ _ _ _ hl he hp, elabC.eq_5 _ _ _ _ _ _ _ hl he hp, hms]
    simp only [hc, if_true]
    exact ih rfl
  · intro held isRoot h args hl he hp hms hc hh; subst hh
    rw [elabC.eq_5 _ _ _ _ _ _ _ hl he hp, elabC.eq_5 _ _ _ _ _ _ _ hl he hp, hms]
    simp [hc]
  · intro held isRoot a h1 h2 h3 h4 h5 hh; subst hh
    rw [elabC.eq_6 _ _ _ _ _ _ h1 h2 h3 h4 h5, elabC.eq_6 _ _ _ _ _ _ h1 h2 h3 h4 h5]
  · intro held p ps a as i acc k hp ih hh; subst hh
    rw [elabArgs.eq_1, elabArgs.eq_1, if_pos hp, if_pos hp]
    exact ih rfl
  · intro held p ps a as i acc k hp iha ihr hh; subst hh
    rw [elabArgs.eq_1, elabArgs.eq_1, if_neg hp, if_neg hp, iha rfl, ihr rfl]
  · intro t held x i acc k hne hh; subst hh
    rw [elabArgs.eq_2 _ _ _ _ _ _ _ _ _ hne, elabArgs.eq_2 _ _ _ _ _ _ _ _ _ hne]

theorem heldVars_nil_of (ps : List Ty) (pats : List Atom) (h : ∀ p ∈ ps, p.holds = false) :
    heldVars ps pats = [] := by
  induction ps generalizing pats with
  | nil => cases pats <;> rfl
  | cons p ps ih =>
      cases pats with
      | nil => rfl
      | cons a as =>
          simp only [heldVars, h p List.mem_cons_self, Bool.false_eq_true, if_false,
            List.nil_append]
          exact ih as fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem elabFn_atom_undef (D : Design) (ha : D.atomBody = true) (ms : Modes) (fn : Fn)
    (noHeld : ∀ p ∈ fn.params, p.holds = false) :
    elabFn D ms (withResult .atom fn) = elabFn D ms (withResult .undef fn) := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => rfl
  | some pr =>
      obtain ⟨ps, r⟩ := pr
      have hps : ∀ p ∈ ps, p.holds = false := noHeld
      show Def.mk h ps.length (ps.map Ty.check) none
          (eqns.map fun e => (e.1, elabBody D ms (heldVars ps e.1) .atom e.2)) =
        Def.mk h ps.length (ps.map Ty.check) none
          (eqns.map fun e => (e.1, elabBody D ms (heldVars ps e.1) .undef e.2))
      congr 1
      apply List.map_congr_left
      intro e _
      rw [heldVars_nil_of ps e.1 hps,
        show elabBody D ms [] .atom e.2 = elabC D ms [] (heldRunsAt D false) true e.2 by
          simp [elabBody, ha],
        show elabBody D ms [] .undef e.2 =
          elabC D ms [] (heldRunsAt D (D.heldUnder .undef)) true e.2 from rfl,
        elabC_heldRun_irrelevant D ms (heldRunsAt D false) (heldRunsAt D (D.heldUnder .undef))
          [] true e.2 rfl]

/-- **The law an evaluated `Atom` result keeps**: where bodies under an `Atom` result are evaluated,
declaring a function's result `Atom` or `%Undefined%` gives the same run at every fuel, for every
program in which that function holds no parameter. (Where a parameter is held, the Prime draft's
root rule separates the two: measured rows 1 and 2.) -/
theorem atom_result_neutral (D : Design) (ha : D.atomBody = true) (P : SProg) (g : String)
    (noHeld : ∀ fn ∈ P, fn.head = g → ∀ p ∈ fn.params, p.holds = false) (n : Nat) (q : Atom) :
    runQ D (setResult P g .atom) n q = runQ D (setResult P g .undef) n q := by
  have hdefs : (setResult P g .atom).map (elabFn D (modesOf P)) =
      (setResult P g .undef).map (elabFn D (modesOf P)) := by
    unfold setResult
    simp only [List.map_map]
    apply List.map_congr_left
    intro fn hfn
    simp only [Function.comp_apply]
    by_cases hg : fn.head = g
    · rw [if_pos hg, if_pos hg]
      exact elabFn_atom_undef D ha _ fn (noHeld fn hfn hg)
    · rw [if_neg hg, if_neg hg]
  have hprog : elabProg D (setResult P g .atom) = elabProg D (setResult P g .undef) := by
    unfold elabProg
    rw [modesOf_setResult, modesOf_setResult, hdefs]
  unfold runQ
  rw [hprog, modesOf_setResult, modesOf_setResult]

/-- The law is not vacuous, and its hypothesis is needed: on `mk` (no held parameter) the Prime
draft gives `(pair 3 4)` under both result types; on the held identity it gives `(f a)` under
`Atom` and `5` under `%Undefined%`. -/
theorem atom_result_neutral_controls :
    runQ primeToday (setResult mkProg "mk" .atom) F qMk =
        runQ primeToday (setResult mkProg "mk" .undef) F qMk ∧
      answers primeToday (setResult mkProg "mk" .atom) F qMk = some [E [S "pair", N 3, N 4]] ∧
      answers primeToday (setResult (rangeProg .atom) "g" .atom) F qRange = some [callFA] ∧
      answers primeToday (setResult (rangeProg .atom) "g" .undef) F qRange = some [N 5] := by
  decide +kernel

/-! ## No hidden state: substituting printed values -/

/-- **Substitution of printed values**: `(let $y M B)` prints what `B` with `M`'s printed value for
`$y` prints. A design that keeps it can be run by rewriting printed text; a design that breaks it
must carry, beside the printed text, which atoms are values (a mark that printing does not show). -/
def KeepsSubstitution (D : Design) : Prop :=
  ∀ (P : SProg) (y : String) (M B v : Atom) (L : List Atom), Prints D P M [v] →
    (Prints D P (E [S "let", V y, M, B]) L ↔ Prints D P (inst [(y, v)] B) L)

/-- The configuration `(let $y (held-atom (f a)) $y)` after binding prints as `(f a)` in every
design, yet its answer is `(f a)` in every value-final design and `5` as source text. -/
theorem valueFinal_designs_break_substitution :
    ¬ KeepsSubstitution byName ∧ ¬ KeepsSubstitution codeValue ∧
      ¬ KeepsSubstitution primeToday ∧ ¬ KeepsSubstitution hybrid := by
  have key : ∀ D : Design, Prints D letProg (E [S "held-atom", callFA]) [callFA] →
      Prints D letProg qLet [callFA] → Prints D letProg callFA [N 5] → ¬ KeepsSubstitution D := by
    intro D hM hlet hv hsub
    have := (hsub letProg "y" (E [S "held-atom", callFA]) (V "y") callFA [callFA] hM).mp hlet
    exact absurd (Prints.det this hv) (by decide)
  refine ⟨key _ ⟨F, ?_⟩ ⟨F, ?_⟩ ⟨F, ?_⟩, key _ ⟨F, ?_⟩ ⟨F, ?_⟩ ⟨F, ?_⟩,
    key _ ⟨F, ?_⟩ ⟨F, ?_⟩ ⟨F, ?_⟩, key _ ⟨F, ?_⟩ ⟨F, ?_⟩ ⟨F, ?_⟩⟩ <;> decide +kernel

/-- Hyperon Experimental substitutes printed values on the measured `let` rows: both sides print
`5`, and `(let $y 3 (pair $y $y))` prints `(pair 3 3)` as its instance does. -/
theorem he_substitution_rows :
    answers he letProg F qLet = some [N 5] ∧
    answers he letProg F (inst [("y", callFA)] (V "y")) = some [N 5] ∧
    answers he letProg F (E [S "let", V "y", N 3, E [S "pair", V "y", V "y"]]) =
      some [E [S "pair", N 3, N 3]] ∧
    answers he letProg F (inst [("y", N 3)] (E [S "pair", V "y", V "y"])) =
      some [E [S "pair", N 3, N 3]] := by
  decide +kernel

/-! ## The named designs against the laws -/

theorem heldRuns_byName : ∀ R, Unchecked R → heldRunsAt byName (byName.heldUnder R) true = true := by
  rintro R (rfl | rfl | rfl) <;> rfl

theorem heldRuns_he : ∀ R, Unchecked R → heldRunsAt he (he.heldUnder R) true = true := by
  rintro R (rfl | rfl | rfl) <;> rfl

theorem heldRuns_primeToday :
    ∀ R, Unchecked R → heldRunsAt primeToday (primeToday.heldUnder R) true = true := by
  rintro R (rfl | rfl | rfl) <;> rfl

theorem byName_laws :
    KeepsWeakening byName ∧ KeepsLet byName ∧ KeepsValuesFinal byName ∧
      KeepsPlainReading byName ∧ KeepsIf byName ∧ KeepsIdentity byName ∧
      KeepsAtomCode byName ∧ ¬ KeepsSubstitution byName :=
  ⟨byName_keeps_weakening, keepsLet_of _ rfl, keepsValuesFinal_of _ rfl,
    keepsPlainReading_of _ heldRuns_byName, keepsIf_of _ heldRuns_byName,
    keepsIdentity_of _ rfl (by rintro R (rfl | rfl | rfl) <;> rfl), keepsAtomCode_of _ rfl,
    valueFinal_designs_break_substitution.1⟩

theorem codeValue_laws :
    KeepsWeakening codeValue ∧ KeepsLet codeValue ∧ KeepsValuesFinal codeValue ∧
      ¬ KeepsPlainReading codeValue ∧ ¬ KeepsIf codeValue ∧ KeepsIdentity codeValue ∧
      KeepsAtomCode codeValue ∧ ¬ KeepsSubstitution codeValue :=
  ⟨codeValue_keeps_weakening, keepsLet_of _ rfl, keepsValuesFinal_of _ rfl,
    codeValue_breaks_plainReading, codeValue_breaks_if,
    keepsIdentity_of _ rfl (by rintro R (rfl | rfl | rfl) <;> rfl), keepsAtomCode_of _ rfl,
    valueFinal_designs_break_substitution.2.1⟩

theorem he_laws :
    KeepsWeakening he ∧ ¬ KeepsLet he ∧ ¬ KeepsValuesFinal he ∧
      KeepsPlainReading he ∧ KeepsIf he ∧ ¬ KeepsIdentity he ∧ KeepsAtomCode he :=
  ⟨he_keeps_weakening, he_breaks_let, he_breaks_valuesFinal,
    keepsPlainReading_of _ heldRuns_he, keepsIf_of _ heldRuns_he, he_breaks_identity,
    keepsAtomCode_of _ rfl⟩

theorem primeToday_laws :
    KeepsWeakening primeToday ∧ KeepsLet primeToday ∧ KeepsValuesFinal primeToday ∧
      KeepsPlainReading primeToday ∧ KeepsIf primeToday ∧ ¬ KeepsIdentity primeToday ∧
      ¬ KeepsAtomCode primeToday ∧ ¬ KeepsSubstitution primeToday :=
  ⟨primeToday_keeps_weakening, keepsLet_of _ rfl, keepsValuesFinal_of _ rfl,
    keepsPlainReading_of _ heldRuns_primeToday, keepsIf_of _ heldRuns_primeToday,
    primeToday_breaks_identity, primeToday_breaks_atomCode,
    valueFinal_designs_break_substitution.2.2.1⟩

end Laws

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
