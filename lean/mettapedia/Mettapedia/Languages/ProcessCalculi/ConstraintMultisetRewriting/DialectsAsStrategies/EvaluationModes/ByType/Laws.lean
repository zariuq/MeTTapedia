import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.ByType.Elab

/-!
# The laws of the typed family, and what each forces

* **Weakening a value result** (`KeepsResultWeakening`): replacing a function's declared result by
  another value type whose check is none or the same changes no run that refused nothing. It holds
  for every program exactly in the designs whose default runs (`resultWeakening_iff`): there a body
  depends on its result type only through the type's mode, so the two elaborations differ only in
  the dropped check (`CoreLaws.exec_weaker`). With the default "pass", `(Code Number)` text returned
  under `Number` runs to `5` and under `%Undefined%` comes back as `(f a)`.
* **Weakening a held annotation** (`KeepsHeldWeakening`): reading every `(Code T)` declaration as
  `Atom` changes no run that refused nothing. In `byType` the two programs elaborate to the same core
  program (`elabProgB_eraseP`), so the runs are equal at every fuel; the other three designs break
  it (`heldWeakening_iff`): with `atomRuns = false`, `Atom` text under `Number` is refused where
  `(Code Number)` text ran; with `dflt = false`, `Atom` text at the code's own type variable passes.
* **No weakening across modes** (`no_cross_mode_weakening`), for any answer function at all: if the
  held identity on `(f a)` answers differently under `Number` and under `(Code Number)`, refusing
  nothing in either, `%Undefined%` cannot be a weakening of both. Every design of the family meets the
  premises (`cross_mode_premises`). So the precision order has two lines, one per mode.
* **`let` and values final** hold in every design of the family, for every program (`runB_let`,
  `runB_myid`).
* **At the root**: in `byType`, a held parameter returned under a value result prints what its text
  prints, for every program and every text (`byType_plain_root`); under a held result it prints its
  text as written, in every design (`inert_held_root`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core CoreLaws Typed Acceptance

namespace ByType

/-! ## Printing -/

theorem runB_mono {td : TDesign} {P : TProg} {q : Atom} {n m : Nat} (le : n ≤ m) {A : List Ans}
    (h : runB td P n q = some A) : runB td P m q = some A :=
  exec_mono _ le _ _ h

theorem answersB_eq (td : TDesign) (P : TProg) (n : Nat) (q : Atom) :
    answersB td P n q = (runB td P n q).map (observe true) := rfl

/-- A query prints at most one list. -/
theorem PrintsB.det {td : TDesign} {P : TProg} {q : Atom} {L L' : List Atom}
    (h : PrintsB td P q L) (h' : PrintsB td P q L') : L = L' := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := h'
  rw [answersB_eq] at hn hm
  cases hA : runB td P n q with
  | none => rw [hA] at hn; exact absurd hn (by simp)
  | some A =>
      cases hB : runB td P m q with
      | none => rw [hB] at hm; exact absurd hm (by simp)
      | some B =>
          rw [hA] at hn
          rw [hB] at hm
          have := exec_det (elabProgB td P) _ hA hB
          subst this
          exact (Option.some.inj hn).symm.trans (Option.some.inj hm)

/-- Two queries print alike when their runs agree, up to the observation, at a fixed difference of
fuel. -/
theorem printsB_iff_of_shift {td : TDesign} {P : TProg} {q q' : Atom} (a b : Nat)
    (shift : ∀ n, (runB td P (n + a) q).map (observe true) =
      (runB td P (n + b) q').map (observe true))
    (L : List Atom) : PrintsB td P q L ↔ PrintsB td P q' L := by
  constructor
  · rintro ⟨n, hn⟩
    rw [answersB_eq] at hn
    cases hA : runB td P n q with
    | none => rw [hA] at hn; exact absurd hn (by simp)
    | some A =>
        rw [hA] at hn
        refine ⟨n + b, ?_⟩
        rw [answersB_eq, ← shift n, runB_mono (by omega) hA]
        exact hn
  · rintro ⟨n, hn⟩
    rw [answersB_eq] at hn
    cases hA : runB td P n q' with
    | none => rw [hA] at hn; exact absurd hn (by simp)
    | some A =>
        rw [hA] at hn
        refine ⟨n + a, ?_⟩
        rw [answersB_eq, shift n, runB_mono (by omega) hA]
        exact hn

/-! ## Weakening a value result -/

/-- Change the declared result type of a function (an undeclared function stays undeclared). -/
def withResultT (R : CTy) (fn : TFn) : TFn :=
  match fn.decl with
  | some (ps, _) => { fn with decl := some (ps, R) }
  | none => fn

/-- Change the declared result type of every function with this head. -/
def setResultT (P : TProg) (g : String) (R : CTy) : TProg :=
  P.map fun fn => if fn.head = g then withResultT R fn else fn

theorem withResultT_head (R : CTy) (fn : TFn) : (withResultT R fn).head = fn.head := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => rfl
  | some p => rfl

theorem withResultT_arity (R : CTy) (fn : TFn) : (withResultT R fn).arity = fn.arity := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => rfl
  | some p => obtain ⟨ps, r⟩ := p; rfl

theorem withResultT_params (R : CTy) (fn : TFn) : (withResultT R fn).params = fn.params := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => rfl
  | some p => obtain ⟨ps, r⟩ := p; rfl

theorem tmodesOf_map (P : TProg) (f : TFn → TFn) (hhead : ∀ fn, (f fn).head = fn.head)
    (harity : ∀ fn, (f fn).arity = fn.arity) :
    tmodesOf (P.map f) = fun h n =>
      ((P.find? fun fn => fn.head == h && fn.arity == n).map fun fn => (f fn).params) := by
  funext h n
  unfold tmodesOf
  rw [List.find?_map]
  have hp : ((fun fn : TFn => fn.head == h && fn.arity == n) ∘ f) =
      fun fn : TFn => fn.head == h && fn.arity == n := by
    funext fn
    simp only [Function.comp_apply, hhead, harity]
  rw [hp]
  cases P.find? (fun fn : TFn => fn.head == h && fn.arity == n) with
  | none => rfl
  | some fn => rfl

theorem tmodesOf_setResultT (P : TProg) (g : String) (R : CTy) :
    tmodesOf (setResultT P g R) = tmodesOf P := by
  unfold setResultT
  rw [tmodesOf_map]
  · funext h n
    unfold tmodesOf
    cases P.find? (fun fn : TFn => fn.head == h && fn.arity == n) with
    | none => rfl
    | some fn =>
        simp only [Option.map_some]
        split <;> simp [withResultT_params]
  · intro fn; split <;> simp [withResultT_head]
  · intro fn; split <;> simp [withResultT_arity]

/-- `R'` is another value type whose check is none or the same. -/
structure ValueWeaker (R R' : CTy) : Prop where
  value : R.holds = false
  value' : R'.holds = false
  check : R'.check = none ∨ R'.check = R.check

/-- Where the default runs, two value types give the same decision. -/
theorem rdOf_value_eq (td : TDesign) (hd : td.dflt = true) (kinds : Held) {E E' : CTy}
    (hE : E.holds = false) (hE' : E'.holds = false) : rdOf td kinds E = rdOf td kinds E' := by
  funext x
  simp only [rdOf, runsAt_dflt td hd _ hE, runsAt_dflt td hd _ hE']

theorem bodyB_weaker (td : TDesign) (hd : td.dflt = true) (ms : TModes) (kinds : Held)
    (held : List String) {R R' : CTy} (w : ValueWeaker R R') (body : Atom) :
    bodyB td ms kinds held R body = bodyB td ms kinds held R' body := by
  rw [bodyB_value td ms kinds held w.value, bodyB_value td ms kinds held w.value']
  unfold elabV
  rw [rdOf_value_eq td hd kinds w.value w.value']

theorem defWeaker_withResultT (td : TDesign) (hd : td.dflt = true) (ms : TModes) {R R' : CTy}
    (w : ValueWeaker R R') (fn : TFn) :
    DefWeaker (elabFnB td ms (withResultT R fn)) (elabFnB td ms (withResultT R' fn)) := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => exact DefWeaker.refl _
  | some p =>
      obtain ⟨ps, r⟩ := p
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩
      · show eqns.map (fun e => (e.1, bodyB td ms (heldTyped ps e.1) (heldNames ps e.1) R' e.2)) =
          eqns.map (fun e => (e.1, bodyB td ms (heldTyped ps e.1) (heldNames ps e.1) R e.2))
        apply List.map_congr_left
        intro e _
        rw [bodyB_weaker td hd ms _ _ w]
      · exact w.check

theorem forall2_setResultT (td : TDesign) (hd : td.dflt = true) (ms : TModes) {R R' : CTy}
    (w : ValueWeaker R R') (g : String) :
    ∀ P : TProg, List.Forall₂ DefWeaker ((setResultT P g R).map (elabFnB td ms))
      ((setResultT P g R').map (elabFnB td ms))
  | [] => .nil
  | fn :: rest => by
      show List.Forall₂ DefWeaker
        (elabFnB td ms (if fn.head = g then withResultT R fn else fn) ::
          (setResultT rest g R).map (elabFnB td ms))
        (elabFnB td ms (if fn.head = g then withResultT R' fn else fn) ::
          (setResultT rest g R').map (elabFnB td ms))
      refine .cons ?_ (forall2_setResultT td hd ms w g rest)
      by_cases h : fn.head = g
      · rw [if_pos h, if_pos h]
        exact defWeaker_withResultT td hd ms w fn
      · rw [if_neg h, if_neg h]
        exact DefWeaker.refl _

theorem progWeaker_setResultT (td : TDesign) (hd : td.dflt = true) {R R' : CTy}
    (w : ValueWeaker R R') (P : TProg) (g : String) :
    ProgWeaker (elabProgB td (setResultT P g R)) (elabProgB td (setResultT P g R')) := by
  refine ⟨?_, ?_⟩
  · show queryB td (setResultT P g R') = queryB td (setResultT P g R)
    unfold queryB
    rw [tmodesOf_setResultT, tmodesOf_setResultT]
  · show List.Forall₂ DefWeaker ((setResultT P g R).map (elabFnB td (tmodesOf (setResultT P g R))))
      ((setResultT P g R').map (elabFnB td (tmodesOf (setResultT P g R'))))
    rw [tmodesOf_setResultT, tmodesOf_setResultT]
    exact forall2_setResultT td hd (tmodesOf P) w g P

/-- **The weakening law for value results.** -/
def KeepsResultWeakening (td : TDesign) : Prop :=
  ∀ (P : TProg) (g : String) (R R' : CTy) (q : Atom) (n : Nat) (L : List Ans), ValueWeaker R R' →
    runB td (setResultT P g R) n q = some L → allVal L = true →
      runB td (setResultT P g R') n q = some L

/-- Every design whose default runs keeps it, for every program. -/
theorem keepsResultWeakening_of (td : TDesign) (hd : td.dflt = true) : KeepsResultWeakening td := by
  intro P g R R' q n L w strong noRefusal
  unfold runB at strong ⊢
  have hq : queryB td (setResultT P g R') q = queryB td (setResultT P g R) q := by
    unfold queryB
    rw [tmodesOf_setResultT, tmodesOf_setResultT]
  rw [hq]
  exact exec_weaker (progWeaker_setResultT td hd w P g) n _ L strong noRefusal

/-- `Number` to `%Undefined%` is such a weakening. -/
theorem number_undef_weaker : ValueWeaker .number .undef := ⟨rfl, rfl, .inl rfl⟩

/-- The counterexample for the default "pass": `(Code Number)` text runs under `Number` and comes back
as written under `%Undefined%`. -/
theorem pass_default_rows (b : Bool) :
    runB ⟨false, b⟩ (setResultT (codeId .number) "g" .number) F qRange =
        some [(.val (N 5), ["g", "f"])] ∧
      runB ⟨false, b⟩ (setResultT (codeId .number) "g" .undef) F qRange =
        some [(.val callFA, ["g"])] := by
  cases b <;> decide +kernel

/-- **The weakening law for value results forces the default "run"**: it holds exactly in the designs
whose default runs. -/
theorem resultWeakening_iff (td : TDesign) : KeepsResultWeakening td ↔ td.dflt = true := by
  constructor
  · intro h
    obtain ⟨d, b⟩ := td
    cases d with
    | true => rfl
    | false =>
        exfalso
        obtain ⟨strong, actual⟩ := pass_default_rows b
        have weak := h _ _ _ _ _ _ _ number_undef_weaker strong (by decide)
        rw [actual] at weak
        exact absurd weak (by decide)
  · exact keepsResultWeakening_of td

/-! ## Weakening a held annotation -/

/-- A declaration with every held type read as `Atom`. -/
def eraseFn (fn : TFn) : TFn :=
  { fn with decl := fn.decl.map fun d => (d.1.map eraseTy, eraseTy d.2) }

/-- A program with every `(Code T)` declaration read as `Atom`. -/
def eraseP (P : TProg) : TProg := P.map eraseFn

theorem eraseFn_head (fn : TFn) : (eraseFn fn).head = fn.head := rfl

theorem eraseFn_arity (fn : TFn) : (eraseFn fn).arity = fn.arity := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => rfl
  | some p => simp [eraseFn, TFn.arity]

theorem eraseFn_params (fn : TFn) : (eraseFn fn).params = fn.params.map eraseTy := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none =>
      simp only [eraseFn, Option.map_none, TFn.params, List.map_replicate]
      rfl
  | some p => simp [eraseFn, TFn.params]

theorem eraseFn_result (fn : TFn) : (eraseFn fn).result = eraseTy fn.result := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => rfl
  | some p => simp [eraseFn, TFn.result]

theorem map_eraseTy_idem (l : List CTy) : (l.map eraseTy).map eraseTy = l.map eraseTy := by
  rw [List.map_map]
  apply List.map_congr_left
  intro T _
  exact eraseTy_eraseTy T

theorem modeView_eraseP (P : TProg) : modeView (tmodesOf (eraseP P)) = modeView (tmodesOf P) := by
  unfold eraseP
  rw [tmodesOf_map P eraseFn eraseFn_head eraseFn_arity]
  funext h n
  unfold modeView tmodesOf
  beta_reduce
  cases P.find? (fun fn : TFn => fn.head == h && fn.arity == n) with
  | none => rfl
  | some fn => simp only [Option.map_some, eraseFn_params, map_eraseTy_idem]

theorem heldNames_erase : ∀ (ps : List CTy) (pats : List Atom),
    heldNames (ps.map eraseTy) pats = heldNames ps pats
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, a :: as => by
      simp only [List.map_cons, heldNames, eraseTy_holds, heldNames_erase ps as]

/-- In `byType` the elaboration of a body sees the declarations only through their modes. -/
theorem bodyB_byType_congr {ms ms' : TModes} (hm : modeView ms = modeView ms') (kinds kinds' : Held)
    (held : List String) (R : CTy) (body : Atom) :
    bodyB byType ms kinds held R body = bodyB byType ms' kinds' held (eraseTy R) body := by
  unfold bodyB elabV
  rw [eraseTy_holds, hm, rdOf_byType, rdOf_byType]
  cases hR : R.holds with
  | true => rfl
  | false => simp [eraseTy_value hR]

theorem elabFnB_byType_erase {ms ms' : TModes} (hm : modeView ms = modeView ms') (fn : TFn) :
    elabFnB byType ms fn = elabFnB byType ms' (eraseFn fn) := by
  unfold elabFnB
  rw [eraseFn_params, eraseFn_result, eraseFn_arity]
  congr 1
  · rw [List.map_map]
    apply List.map_congr_left
    intro T _
    exact (eraseTy_check T).symm
  · rw [eraseTy_check]
  · show fn.eqns.map _ = fn.eqns.map _
    apply List.map_congr_left
    intro e _
    rw [heldNames_erase, bodyB_byType_congr hm]

/-- **Held annotations are read only through their mode in `byType`**: reading every `(Code T)`
declaration as `Atom` gives the same core program. -/
theorem elabProgB_eraseP (P : TProg) : elabProgB byType (eraseP P) = elabProgB byType P := by
  unfold elabProgB
  congr 1
  · unfold eraseP
    rw [List.map_map]
    apply List.map_congr_left
    intro fn _
    exact (elabFnB_byType_erase (modeView_eraseP P).symm fn).symm
  · funext q
    unfold queryB elabV
    rw [modeView_eraseP]

/-- So every run is the same, at every fuel. -/
theorem runB_eraseP (P : TProg) (n : Nat) (q : Atom) :
    runB byType (eraseP P) n q = runB byType P n q := by
  unfold runB
  rw [elabProgB_eraseP]
  unfold queryB elabV
  rw [modeView_eraseP]

/-- **The weakening law for held annotations.** -/
def KeepsHeldWeakening (td : TDesign) : Prop :=
  ∀ (P : TProg) (n : Nat) (q : Atom) (L : List Ans), runB td P n q = some L → allVal L = true →
    runB td (eraseP P) n q = some L

theorem byType_keepsHeldWeakening : KeepsHeldWeakening byType := by
  intro P n q L h _
  rw [runB_eraseP]
  exact h

/-- `(: g (-> (Code $t) $t)) (= (g $x) $x)`. -/
def codeVarId : TProg := [tfA, heldIdT "g" (.code (.var "t")) (.var "t")]

/-- The counterexamples: with `atomRuns = false`, `Atom` text under `Number` is refused where
`(Code Number)` text ran; with `dflt = false`, `Atom` text at a type variable passes where
`(Code $t)` text at its own `$t` ran. -/
theorem heldWeakening_rows :
    runB codeOnly (codeId .number) F qRange = some [(.val (N 5), ["g", "f"])] ∧
    runB codeOnly (eraseP (codeId .number)) F qRange = some [(.refused callFA .number, ["g"])] ∧
    runB typedPass (codeId .number) F qRange = some [(.val (N 5), ["g", "f"])] ∧
    runB typedPass (eraseP (codeId .number)) F qRange = some [(.refused callFA .number, ["g"])] ∧
    runB atomPass codeVarId F qRange = some [(.val (N 5), ["g", "f"])] ∧
    runB atomPass (eraseP codeVarId) F qRange = some [(.val callFA, ["g"])] := by
  decide +kernel

/-- **The weakening law for held annotations holds exactly in `byType`.** -/
theorem heldWeakening_iff (td : TDesign) : KeepsHeldWeakening td ↔ td = byType := by
  constructor
  · intro h
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := heldWeakening_rows
    obtain ⟨d, b⟩ := td
    cases d <;> cases b
    · have := h _ _ _ _ r3 (by decide)
      exact absurd (this.symm.trans r4) (by decide)
    · have := h _ _ _ _ r5 (by decide)
      exact absurd (this.symm.trans r6) (by decide)
    · have := h _ _ _ _ r1 (by decide)
      exact absurd (this.symm.trans r2) (by decide)
    · rfl
  · rintro rfl
    exact byType_keepsHeldWeakening

/-! ## No weakening across modes -/

/-- Core answers of queries in typed programs (a design at some fuel, or anything else). -/
abbrev TAnswerFn := TProg → Atom → Option (List Ans)

/-- **`%Undefined%` cannot weaken both `Number` and `(Code Number)`**, for any answer function: the
two weakening steps would give one query two different answers. -/
theorem no_cross_mode_weakening (A : TAnswerFn)
    (wNumber : ∀ L, A (codeId .number) qRange = some L → allVal L = true →
      A (codeId .undef) qRange = some L)
    (wCode : ∀ L, A (codeId (.code .number)) qRange = some L → allVal L = true →
      A (codeId .undef) qRange = some L)
    {L1 L2 : List Ans} (h1 : A (codeId .number) qRange = some L1) (v1 : allVal L1 = true)
    (h2 : A (codeId (.code .number)) qRange = some L2) (v2 : allVal L2 = true) (ne : L1 ≠ L2) :
    False :=
  ne (Option.some.inj ((wNumber L1 h1 v1).symm.trans (wCode L2 h2 v2)))

/-- Every design of the family meets the premises: under `Number` the text runs to `5`, under
`(Code Number)` it comes back as written, refusing nothing. -/
theorem cross_mode_premises (td : TDesign) :
    runB td (codeId .number) F qRange = some [(.val (N 5), ["g", "f"])] ∧
      runB td (codeId (.code .number)) F qRange = some [(.val callFA, ["g"])] := by
  obtain ⟨d, b⟩ := td
  cases d <;> cases b <;> decide +kernel

/-! ## `let` and values final, in every design -/

/-- With nothing held, the decision at the current position is never consulted. -/
theorem elabW_held_nil (ms : TModes) (rd : CTy → String → Bool) :
    ∀ (held : List String) (r : String → Bool) (t : Atom), held = [] → ∀ r' : String → Bool,
      elabW ms rd held r t = elabW ms rd held r' t := by
  intro held r t
  refine elabW.induct ms rd
    (motive_1 := fun held r t => held = [] → ∀ r' : String → Bool,
      elabW ms rd held r t = elabW ms rd held r' t)
    (motive_2 := fun _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ held r t
  · intro held r x _ hh r'; subst hh; simp [elabW]
  · intro held r x _ hh r'; subst hh; simp [elabW]
  · intro held r y src body _ ihb hh r'; subst hh
    rw [elabW.eq_2, elabW.eq_2, ihb (by simp) r']
  · intro held r m _ _ r'; rw [elabW.eq_3, elabW.eq_3]
  · intro held r a b _ _ _ r'; rw [elabW.eq_4, elabW.eq_4]
  · intro held r h args hl he hp _ _ _ _ r'
    rw [elabW.eq_5 _ _ _ _ _ _ hl he hp, elabW.eq_5 _ _ _ _ _ _ hl he hp]
  · intro held r h args hl he hp _ _ _ r'
    rw [elabW.eq_5 _ _ _ _ _ _ hl he hp, elabW.eq_5 _ _ _ _ _ _ hl he hp]
  · intro held r a h1 h2 h3 h4 h5 _ r'
    rw [elabW.eq_6 _ _ _ _ _ h1 h2 h3 h4 h5, elabW.eq_6 _ _ _ _ _ h1 h2 h3 h4 h5]
  · intros; trivial
  · intros; trivial
  · intros; trivial

theorem queryB_let (td : TDesign) (P : TProg) (y : String) (M : Atom) :
    queryB td P (Laws.letQ y M) = .bind (queryB td P M) y (.ret (.var y)) := by
  unfold queryB elabV Laws.letQ
  rw [show (E [S "let", V y, M, V y] : Atom) = .expression [.symbol "let", .var y, M, .var y]
    from rfl, elabW.eq_2]
  simp [elabW]

/-- **`let` in every design of the family**: `(let $y M $y)` runs as `M`, one step later. -/
theorem runB_let (td : TDesign) (P : TProg) (y : String) (M : Atom) (n : Nat) :
    runB td P (n + 2) (Laws.letQ y M) = runB td P (n + 1) M := by
  unfold runB
  rw [queryB_let]
  exact exec_bind_ret _ _ _ _ _

theorem keepsLet (td : TDesign) (P : TProg) (y : String) (M : Atom) (L : List Atom) :
    PrintsB td P (Laws.letQ y M) L ↔ PrintsB td P M L := by
  apply printsB_iff_of_shift 2 1
  intro n
  rw [runB_let]

/-- `(: myid (-> T T)) (= (myid $z) $z)`. -/
def valueIdT (T : CTy) : TFn := ⟨"myid", some ([T], T), [([V "z"], V "z")]⟩

/-- The computation types whose parameters run without a check. -/
def UncheckedT (T : CTy) : Prop := T = .proc ∨ T = .undef ∨ ∃ a, T = .var a

theorem uncheckedT_value {T : CTy} (h : UncheckedT T) : T.holds = false ∧ T.check = none := by
  rcases h with rfl | rfl | ⟨a, rfl⟩ <;> exact ⟨rfl, rfl⟩

theorem queryB_myid (td : TDesign) (T : CTy) (hT : UncheckedT T) (P0 : TProg) (M : Atom) :
    queryB td (valueIdT T :: P0) (Laws.idQ M) =
      .bind (queryB td (valueIdT T :: P0) M) (slot 0) (.call "myid" [.var (slot 0)]) := by
  obtain ⟨hv, _⟩ := uncheckedT_value hT
  have hms : modeView (tmodesOf (valueIdT T :: P0)) "myid" 1 = some [eraseTy T] := by
    simp [modeView, tmodesOf, valueIdT, TFn.arity, TFn.params]
  unfold queryB elabV Laws.idQ
  rw [show (E [S "myid", M] : Atom) = .expression [.symbol "myid", M] from rfl,
    elabW.eq_5 _ _ _ _ _ _ (by intros; simp_all) (by intros; simp_all) (by intros; simp_all)]
  simp only [List.length_singleton, hms]
  rw [elabArgsW_value _ _ _ (by rw [eraseTy_holds]; exact hv), eraseTy_value hv,
    elabW_held_nil _ _ [] (rdOf td [] T) M rfl (rdOf td [] .undef)]
  rfl

/-- **Values are final, in every design of the family**: through an evaluated identity typed
`Proc`, `%Undefined%` or a type variable, `(myid M)` runs as `M`, its answers marked by `myid`. -/
theorem runB_myid (td : TDesign) (T : CTy) (hT : UncheckedT T) (P0 : TProg) (M : Atom)
    (m : Nat) :
    runB td (valueIdT T :: P0) (m + 4) (Laws.idQ M) =
      (runB td (valueIdT T :: P0) (m + 3) M).map fun L =>
        L.map fun a => match a with
          | (.val v, trace) => (.val v, trace ++ ["myid"])
          | (.refused d k, trace) => (.refused d k, trace) := by
  obtain ⟨hv, hc⟩ := uncheckedT_value hT
  have hk : (fun v => exec (elabProgB td (valueIdT T :: P0)) (m + 3)
      (.comp [(slot 0, v)] (.call "myid" [.var (slot 0)]))) =
      fun v => some [(.val v, ["myid"])] := by
    funext v
    rw [exec_call]
    simp only [List.map, inst_var_head]
    have hcl : (elabFnB td (tmodesOf (valueIdT T :: P0)) (valueIdT T)).clauses =
        [([.var "z"], .ret (.var "z"))] := by
      show [([Atom.var "z"], bodyB td (tmodesOf (valueIdT T :: P0)) (heldTyped [T] [V "z"])
        (heldNames [T] [V "z"]) T (V "z"))] = _
      rw [bodyB_value _ _ _ _ hv]
      have hn : heldNames [T] [V "z"] = [] := by simp [heldNames, hv]
      rw [hn]
      simp [elabV, elabW, V]
    rw [Laws.exec_enter_first _ "myid" [v] _ [.var "z"] (.ret (.var "z")) [] [("z", v)] (m + 1)
      (by simp [Prog.find, elabProgB, valueIdT, elabFnB, TFn.arity])
      (by simp [valueIdT, elabFnB, TFn.params, firstRefusal, hc]) (by
        simp [elabFnB, valueIdT, TFn.result, hc]) hcl rfl fun _ => rfl]
    rfl
  unfold runB
  rw [queryB_myid td T hT P0 M, exec_bind, hk]
  cases exec _ (m + 3) _ with
  | none => rfl
  | some L => exact continueEach_single L "myid"

theorem keepsValuesFinal (td : TDesign) (T : CTy) (hT : UncheckedT T) (P0 : TProg) (M : Atom)
    (L : List Atom) :
    PrintsB td (valueIdT T :: P0) (Laws.idQ M) L ↔ PrintsB td (valueIdT T :: P0) M L := by
  apply printsB_iff_of_shift 4 3
  intro n
  rw [runB_myid td T hT P0 M n]
  cases runB td (valueIdT T :: P0) (n + 3) M with
  | none => rfl
  | some A => simp only [Option.map_some]; congr 1; exact observe_appendTrace _ A "myid"

/-! ## A held parameter returned at the root -/

theorem check_of_holds {T : CTy} (h : T.holds = true) : T.check = none := by
  cases T <;> simp_all [CTy.holds, CTy.check]

theorem queryB_g (td : TDesign) {H : CTy} (hH : H.holds = true) (B : Atom) (R : CTy)
    (P0 : TProg) (M : Atom) :
    queryB td (heldBodyT "g" H R B :: P0) (Laws.gQ M) = .call "g" [M] := by
  have hms : modeView (tmodesOf (heldBodyT "g" H R B :: P0)) "g" 1 = some [eraseTy H] := by
    simp [modeView, tmodesOf, heldBodyT, TFn.arity, TFn.params]
  unfold queryB elabV Laws.gQ
  rw [show (E [S "g", M] : Atom) = .expression [.symbol "g", M] from rfl,
    elabW.eq_5 _ _ _ _ _ _ (by intros; simp_all) (by intros; simp_all) (by intros; simp_all)]
  simp only [List.length_singleton, hms]
  rw [elabArgsW_held _ _ _ (by rw [eraseTy_holds]; exact hH)]
  rfl

theorem find_heldBodyT (td : TDesign) (H R : CTy) (B : Atom) (P0 : TProg) :
    (elabProgB td (heldBodyT "g" H R B :: P0)).find "g" 1 =
      some (elabFnB td (tmodesOf (heldBodyT "g" H R B :: P0)) (heldBodyT "g" H R B)) := by
  simp [Prog.find, elabProgB, heldBodyT, elabFnB, TFn.arity]

/-- The held identity returned under a value result, in any design: the text runs exactly when
the design's decision says so at that result type. -/
theorem runB_heldId (td : TDesign) {H : CTy} (hH : H.holds = true) {R : CTy}
    (hR : R.holds = false) (hRc : R.check = none) (P0 : TProg) (M : Atom) (m : Nat) :
    runB td (heldBodyT "g" H R (V "x") :: P0) (m + 4) (Laws.gQ M) =
      if rdOf td (heldTyped [H] [V "x"]) R "x" then
        (runB td (heldBodyT "g" H R (V "x") :: P0) (m + 1) M).map
          (List.map (Laws.prefixTrace "g"))
      else some [(.val M, ["g"])] := by
  have hcl : (elabFnB td (tmodesOf (heldBodyT "g" H R (V "x") :: P0))
      (heldBodyT "g" H R (V "x"))).clauses =
      [([.var "x"], if rdOf td (heldTyped [H] [V "x"]) R "x" then .run (.var "x")
        else .ret (.var "x"))] := by
    show [([Atom.var "x"], bodyB td (tmodesOf (heldBodyT "g" H R (V "x") :: P0))
      (heldTyped [H] [V "x"]) (heldNames [H] [V "x"]) R (V "x"))] = _
    rw [bodyB_value _ _ _ _ hR]
    have hn : heldNames [H] [V "x"] = ["x"] := by simp [heldNames, hH, patVars, V]
    rw [hn]
    unfold elabV
    by_cases hc : rdOf td (heldTyped [H] [V "x"]) R "x" = true <;> simp_all [elabW, V]
  unfold runB
  rw [queryB_g td hH (V "x") R P0 M, exec_call]
  simp only [List.map, inst_nil]
  rw [Laws.exec_enter_first _ "g" [M] _ [.var "x"] _ [] [("x", M)] (m + 2)
    (find_heldBodyT td H R (V "x") P0)
    (by simp [elabFnB, heldBodyT, TFn.params, firstRefusal, check_of_holds hH])
    (by simp [elabFnB, heldBodyT, TFn.result, hRc]) hcl rfl fun _ => rfl]
  by_cases hc : rdOf td (heldTyped [H] [V "x"]) R "x" = true
  · rw [if_pos hc, if_pos hc, exec_run, inst_var_head]
    rfl
  · rw [if_neg hc, if_neg hc]
    rfl

/-- **The plain reading at the root, in `byType`**: a held parameter (`Atom` or `(Code T)`)
returned under an unchecked value result prints what its text prints, for every program and every
text. -/
theorem byType_plain_root {H : CTy} (hH : H.holds = true) {R : CTy} (hR : R.holds = false)
    (hRc : R.check = none) (P0 : TProg) (M : Atom) (L : List Atom) :
    PrintsB byType (heldBodyT "g" H R (V "x") :: P0) (Laws.gQ M) L ↔
      PrintsB byType (heldBodyT "g" H R (V "x") :: P0) M L := by
  apply printsB_iff_of_shift 4 1
  intro n
  rw [runB_heldId byType hH hR hRc P0 M n, if_pos (by simp [rdOf_byType, hR])]
  cases runB byType (heldBodyT "g" H R (V "x") :: P0) (n + 1) M with
  | none => rfl
  | some A => simp only [Option.map_some]; congr 1; exact Laws.observe_prefix _ "g" A

/-- Under a held result the body is returned as written, with the argument's text for the
parameter, in every design. -/
theorem runB_heldResult (td : TDesign) {H R : CTy} (hH : H.holds = true) (hR : R.holds = true)
    (B : Atom) (P0 : TProg) (M : Atom) :
    runB td (heldBodyT "g" H R B :: P0) 3 (Laws.gQ M) =
      some [(.val (inst [("x", M)] B), ["g"])] := by
  have hcl : (elabFnB td (tmodesOf (heldBodyT "g" H R B :: P0)) (heldBodyT "g" H R B)).clauses =
      [([.var "x"], .ret B)] := by
    show [([Atom.var "x"], bodyB td (tmodesOf (heldBodyT "g" H R B :: P0))
      (heldTyped [H] [V "x"]) (heldNames [H] [V "x"]) R B)] = _
    rw [bodyB_held _ _ _ _ hR]
  unfold runB
  rw [queryB_g td hH B R P0 M, exec_call]
  simp only [List.map, inst_nil]
  rw [Laws.exec_enter_first _ "g" [M] _ [.var "x"] _ [] [("x", M)] 1
    (find_heldBodyT td H R B P0)
    (by simp [elabFnB, heldBodyT, TFn.params, firstRefusal, check_of_holds hH])
    (by simp [elabFnB, heldBodyT, TFn.result, check_of_holds hR]) hcl rfl fun _ => rfl]
  rfl

/-- **Inert at held positions, in every design**: `(g M)` prints the body with `M`'s text for the
parameter, as written; for the bare body `$x`, it prints `M`. -/
theorem inert_held_root (td : TDesign) {H R : CTy} (hH : H.holds = true) (hR : R.holds = true)
    (B : Atom) (P0 : TProg) (M : Atom) :
    PrintsB td (heldBodyT "g" H R B :: P0) (Laws.gQ M) [inst [("x", M)] B] :=
  ⟨3, by rw [answersB_eq, runB_heldResult td hH hR B P0 M]; rfl⟩

end ByType

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
