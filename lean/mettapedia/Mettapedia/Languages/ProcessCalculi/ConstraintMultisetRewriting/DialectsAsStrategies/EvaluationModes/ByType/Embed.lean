import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.ByType.Laws

/-!
# Both surviving designs inside the typed family, exactly

The study's surface (`Designs.SProg`) translates into the typed one (`embedP`): every type keeps its
name, the one type variable becomes `$t`, a `(Code T)` parameter becomes `Atom` (in the study it is
elaborated exactly as `Atom`), and a `(Code T)` result becomes `%Undefined%` (in the study it is a
computation type without a check).

* `elabC_eq_elabW`: for a design whose values are final and whose undeclared heads evaluate their
  arguments, the study's elaboration with a constant held rule `b` is the typed elaboration whose
  decision at every value position is `b`. One induction over the study's elaborator.
* **By-name is `byType` on the study's programs** (`byName_eq_byType`): the elaborated core programs
  are equal, so every run is equal at every fuel, for every program and every query; no hypothesis.
* **Code value is `codeOnly` on the study's programs** (`codeValue_eq_codeOnly`): equal core programs
  likewise (code value prints a refusal as no answer, `codeOnly` as an error atom; the runs are equal).
* **The converse** (`byType_eq_byName_proj`): every typed program, run in `byType`, is the by-name run
  of its projection to the study's surface (`(Code T)` read as `Atom`, type variables as the study's
  one variable). So `byType` adds no evaluation behaviour to by-name: the `(Code T)` types are static
  information, and inertness comes from held positions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core CoreLaws Typed Acceptance

namespace ByType

/-! ## The translations between the surfaces -/

/-- A study type as a typed one. -/
def embedTy : Ty → CTy
  | .atom => .atom
  | .proc => .proc
  | .number => .number
  | .bool => .bool
  | .undef => .undef
  | .tvar => .var "t"
  | .code _ => .atom

/-- A study result type as a typed one: a `(Code T)` result is a computation type there. -/
def embedRes : Ty → CTy
  | .code _ => .undef
  | T => embedTy T

/-- A study function as a typed one. -/
def embedFn (fn : Fn) : TFn :=
  ⟨fn.head, fn.decl.map fun d => (d.1.map embedTy, embedRes d.2), fn.eqns⟩

/-- A study program as a typed one. -/
def embedP (P : SProg) : TProg := P.map embedFn

/-- A typed type as a study one: held types as `Atom`, type variables as the study's variable. -/
def projTy : CTy → Ty
  | .number => .number
  | .bool => .bool
  | .proc => .proc
  | .undef => .undef
  | .atom => .atom
  | .var _ => .tvar
  | .code _ => .atom

/-- A typed function as a study one. -/
def projFn (fn : TFn) : Fn :=
  ⟨fn.head, fn.decl.map fun d => (d.1.map projTy, projTy d.2), fn.eqns⟩

/-- A typed program as a study one. -/
def projP (P : TProg) : SProg := P.map projFn

theorem embedTy_holds (T : Ty) : (embedTy T).holds = T.holds := by cases T <;> rfl

/-- A translated result holds exactly when it was `Atom`: a study `(Code T)` result is a computation
type there (its body is evaluated), though a `(Code T)` parameter holds. -/
theorem embedRes_holds_iff (R : Ty) : (embedRes R).holds = true ↔ R = .atom := by
  cases R <;> simp [embedRes, embedTy, CTy.holds]
theorem embedTy_check (T : Ty) : (embedTy T).check = T.check := by cases T <;> rfl
theorem embedRes_check (T : Ty) : (embedRes T).check = T.check := by cases T <;> rfl
theorem projTy_holds (T : CTy) : (projTy T).holds = T.holds := by cases T <;> rfl
theorem projTy_check (T : CTy) : (projTy T).check = T.check := by cases T <;> rfl

theorem embedFn_arity (fn : Fn) : (embedFn fn).arity = fn.arity := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => rfl
  | some p => simp [embedFn, TFn.arity, Fn.arity]

theorem embedFn_params (fn : Fn) : (embedFn fn).params = fn.params.map embedTy := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none =>
      simp only [embedFn, Option.map_none, TFn.params, Fn.params, List.map_replicate]
      rfl
  | some p => simp [embedFn, TFn.params, Fn.params]

theorem embedFn_result (fn : Fn) : (embedFn fn).result = embedRes fn.result := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => rfl
  | some p => simp [embedFn, TFn.result, Fn.result]

theorem projFn_arity (fn : TFn) : (projFn fn).arity = fn.arity := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => rfl
  | some p => simp [projFn, TFn.arity, Fn.arity]

theorem projFn_params (fn : TFn) : (projFn fn).params = fn.params.map projTy := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none =>
      simp only [projFn, Option.map_none, TFn.params, Fn.params, List.map_replicate]
      rfl
  | some p => simp [projFn, TFn.params, Fn.params]

theorem projFn_result (fn : TFn) : (projFn fn).result = projTy fn.result := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => rfl
  | some p => simp [projFn, TFn.result, Fn.result]

theorem tmodesOf_embedP (P : SProg) :
    tmodesOf (embedP P) = fun h n => (modesOf P h n).map (List.map embedTy) := by
  funext h n
  unfold tmodesOf modesOf embedP
  rw [List.find?_map]
  have hp : ((fun fn : TFn => fn.head == h && fn.arity == n) ∘ embedFn) =
      fun fn : Fn => fn.head == h && fn.arity == n := by
    funext fn
    simp only [Function.comp_apply, embedFn_arity]
    rfl
  rw [hp]
  cases P.find? (fun fn : Fn => fn.head == h && fn.arity == n) with
  | none => rfl
  | some fn => simp [embedFn_params]

theorem modesOf_projP (P : TProg) :
    modesOf (projP P) = fun h n => (tmodesOf P h n).map (List.map projTy) := by
  funext h n
  unfold tmodesOf modesOf projP
  rw [List.find?_map]
  have hp : ((fun fn : Fn => fn.head == h && fn.arity == n) ∘ projFn) =
      fun fn : TFn => fn.head == h && fn.arity == n := by
    funext fn
    simp only [Function.comp_apply, projFn_arity]
    rfl
  rw [hp]
  cases P.find? (fun fn : TFn => fn.head == h && fn.arity == n) with
  | none => rfl
  | some fn => simp [projFn_params]

/-! ## Modes that match -/

/-- Two parameter lists that hold at the same places. -/
def HoldsMatch (ps : List Ty) (ps' : List CTy) : Prop :=
  List.Forall₂ (fun p p' => p.holds = p'.holds) ps ps'

/-- The study's modes and the typed ones declare the same heads, holding at the same places. -/
def ModesMatch (ms : Modes) (msW : TModes) : Prop :=
  ∀ h n, (ms h n = none ∧ msW h n = none) ∨
    ∃ ps ps', ms h n = some ps ∧ msW h n = some ps' ∧ HoldsMatch ps ps'

theorem holdsMatch_embed (ps : List Ty) : HoldsMatch ps ((ps.map embedTy).map eraseTy) := by
  induction ps with
  | nil => exact .nil
  | cons p ps ih => exact .cons (by simp [eraseTy_holds, embedTy_holds]) ih

theorem holdsMatch_proj (ps : List CTy) : HoldsMatch (ps.map projTy) (ps.map eraseTy) := by
  induction ps with
  | nil => exact .nil
  | cons p ps ih => exact .cons (by simp [eraseTy_holds, projTy_holds]) ih

theorem holdsMatch_replicate (n : Nat) :
    HoldsMatch (List.replicate n Ty.undef) (List.replicate n CTy.undef) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons rfl ih

theorem modesMatch_embed (P : SProg) :
    ModesMatch (modesOf P) (modeView (tmodesOf (embedP P))) := by
  intro h n
  have e : modeView (tmodesOf (embedP P)) h n =
      ((modesOf P h n).map (List.map embedTy)).map (List.map eraseTy) := by
    rw [tmodesOf_embedP]; rfl
  rw [e]
  cases modesOf P h n with
  | none => exact .inl ⟨rfl, rfl⟩
  | some ps => exact .inr ⟨ps, _, rfl, rfl, holdsMatch_embed ps⟩

theorem modesMatch_proj (P : TProg) :
    ModesMatch (modesOf (projP P)) (modeView (tmodesOf P)) := by
  intro h n
  have e : modesOf (projP P) h n = (tmodesOf P h n).map (List.map projTy) := by
    rw [modesOf_projP]
  rw [e]
  unfold modeView
  cases tmodesOf P h n with
  | none => exact .inl ⟨rfl, rfl⟩
  | some ps => exact .inr ⟨_, _, rfl, rfl, holdsMatch_proj ps⟩

/-! ## One induction over the study's elaborator -/

/-- **The study's elaboration with a constant held rule is the typed elaboration with that constant
decision**, for a design whose values are final and whose undeclared heads evaluate arguments. -/
theorem elabC_eq_elabW (D : Design) (hrv : D.rerunValues = false)
    (hc : D.constructorsRun = true) (b : Bool) (ms : Modes) (msW : TModes)
    (hms : ModesMatch ms msW) (rd : CTy → String → Bool)
    (hrd : ∀ E : CTy, E.holds = false → rd E = fun _ => b) :
    ∀ (held : List String) (isRoot : Bool) (t : Atom),
      elabC D ms held (fun _ => b) isRoot t = elabW msW rd held (fun _ => b) t := by
  intro held isRoot t
  refine elabC.induct D ms
    (motive_1 := fun held isRoot t =>
      elabC D ms held (fun _ => b) isRoot t = elabW msW rd held (fun _ => b) t)
    (motive_2 := fun held ps args i acc k => ∀ ps' : List CTy, HoldsMatch ps ps' →
      elabArgs D ms held (fun _ => b) ps args i acc k = elabArgsW msW rd held ps' args i acc k)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ held isRoot t
  · intro held isRoot x
    rw [elabC.eq_1, elabW.eq_1]
    unfold elabVar
    rw [hrv]
    cases held.contains x <;> cases b <;> rfl
  · intro held isRoot y src body ihs ihb
    rw [elabC.eq_2, elabW.eq_2, hrd .undef rfl, ihs, ihb]
  · intro held isRoot m ih
    rw [elabC.eq_3, elabW.eq_3, hrd .undef rfl, ih]
  · intro held isRoot a1 a2 ih1 ih2
    rw [elabC.eq_4, elabW.eq_4, hrd .number rfl, ih1, ih2]
  · intro held isRoot h args hl he hp ps hps ih
    rw [elabC.eq_5 _ _ _ _ _ _ _ hl he hp, elabW.eq_5 _ _ _ _ _ _ hl he hp, hps]
    rcases hms h args.length with ⟨h1, _⟩ | ⟨ps1, ps', h1, h2, hm⟩
    · rw [hps] at h1; cases h1
    · rw [hps] at h1
      cases h1
      rw [h2]
      exact ih ps' hm
  · intro held isRoot h args hl he hp hnone hcr ih
    rw [elabC.eq_5 _ _ _ _ _ _ _ hl he hp, elabW.eq_5 _ _ _ _ _ _ hl he hp, hnone]
    rcases hms h args.length with ⟨_, h2⟩ | ⟨ps1, ps', h1, _, _⟩
    · rw [h2]
      simp only [hcr, if_true]
      exact ih _ (holdsMatch_replicate args.length)
    · rw [hnone] at h1; cases h1
  · intro held isRoot h args hl he hp hnone hcr
    exact absurd hc hcr
  · intro held isRoot a h1 h2 h3 h4 h5
    rw [elabC.eq_6 _ _ _ _ _ _ h1 h2 h3 h4 h5, elabW.eq_6 _ _ _ _ _ h1 h2 h3 h4 h5]
  · intro held p ps a as i acc k hp ih ps' hm
    cases hm with
    | cons hpp hm' =>
        rw [elabArgs.eq_1, if_pos hp, elabArgsW_held _ _ _ (by rw [← hpp]; exact hp)]
        exact ih _ hm'
  · intro held p ps a as i acc k hp iha ihr ps' hm
    cases hm with
    | cons hpp hm' =>
        have hp' : p.holds = false := by simpa using hp
        rw [elabArgs.eq_1, if_neg hp, elabArgsW_value _ _ _ (by rw [← hpp]; exact hp'),
          hrd _ (by rw [← hpp]; exact hp'), iha, ihr _ hm']
  · intro t held x i acc k hne ps' hm
    rw [elabArgs.eq_2 _ _ _ _ _ _ _ _ _ hne, elabArgsW.eq_2 _ _ _ _ _ _ _ _ (by
      intro p' ps'' a as h1 h2
      subst h1
      cases hm with
      | cons _ _ => exact hne _ _ a as rfl h2)]

/-! ## Clauses and programs -/

theorem heldNames_embed : ∀ (ps : List Ty) (pats : List Atom),
    heldNames (ps.map embedTy) pats = heldVars ps pats
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, a :: as => by
      simp only [List.map_cons, heldNames, heldVars, embedTy_holds, heldNames_embed ps as]

theorem heldVars_proj : ∀ (ps : List CTy) (pats : List Atom),
    heldVars (ps.map projTy) pats = heldNames ps pats
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, a :: as => by
      simp only [List.map_cons, heldNames, heldVars, projTy_holds, heldVars_proj ps as]

theorem lookup_getD_none (x : String) :
    ∀ (l : Held), (∀ p ∈ l, p.2 = none) → (l.lookup x).getD none = none
  | [], _ => rfl
  | (y, v) :: rest, h => by
      unfold List.lookup
      split
      · simpa using h (y, v) List.mem_cons_self
      · exact lookup_getD_none x rest (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem heldTyped_embed_snd : ∀ (ps : List Ty) (pats : List Atom) (p : String × Option CTy),
    p ∈ heldTyped (ps.map embedTy) pats → p.2 = none
  | [], _, p, hp => by simp [heldTyped] at hp
  | _ :: _, [], p, hp => by simp [heldTyped] at hp
  | q :: qs, a :: as, p, hp => by
      have rest := heldTyped_embed_snd qs as p
      cases q with
      | atom =>
          simp only [List.map_cons, embedTy, heldTyped, List.mem_append, List.mem_map] at hp
          rcases hp with ⟨y, _, rfl⟩ | hp
          · rfl
          · exact rest hp
      | code U =>
          simp only [List.map_cons, embedTy, heldTyped, List.mem_append, List.mem_map] at hp
          rcases hp with ⟨y, _, rfl⟩ | hp
          · rfl
          · exact rest hp
      | proc =>
          simp only [List.map_cons, embedTy, heldTyped, List.nil_append] at hp
          exact rest hp
      | number =>
          simp only [List.map_cons, embedTy, heldTyped, List.nil_append] at hp
          exact rest hp
      | bool =>
          simp only [List.map_cons, embedTy, heldTyped, List.nil_append] at hp
          exact rest hp
      | undef =>
          simp only [List.map_cons, embedTy, heldTyped, List.nil_append] at hp
          exact rest hp
      | tvar =>
          simp only [List.map_cons, embedTy, heldTyped, List.nil_append] at hp
          exact rest hp

/-- A translated study clause binds only `Atom` held variables. -/
theorem kindOf_embed (ps : List Ty) (pats : List Atom) (x : String) :
    kindOf (heldTyped (ps.map embedTy) pats) x = none :=
  lookup_getD_none x _ (heldTyped_embed_snd ps pats)

/-- The study's body under a result type, for a design with `Atom` bodies quoted and a constant
held rule `b` under the computation types. -/
theorem elabBody_eq (D : Design) (hrv : D.rerunValues = false) (hc : D.constructorsRun = true)
    (ha : D.atomBody = false) (b : Bool)
    (hb : ∀ R : Ty, R ≠ .atom → heldRunsAt D (D.heldUnder R) = fun _ => b)
    (ms : Modes) (msW : TModes) (hms : ModesMatch ms msW) (rd : CTy → String → Bool)
    (hrd : ∀ E : CTy, E.holds = false → rd E = fun _ => b) (held : List String) (R : Ty)
    (R' : CTy) (hRR : R'.holds = true ↔ R = .atom) (body : Atom) :
    elabBody D ms held R body =
      if R'.holds then .ret body else elabW msW rd held (rd R') body := by
  by_cases hR : R = .atom
  · subst hR
    simp only [elabBody, ha, Bool.false_eq_true, if_false]
    rw [if_pos (hRR.mpr rfl)]
  · have hRv : R'.holds = false := by
      cases h : R'.holds
      · rfl
      · exact absurd (hRR.mp h) hR
    rw [if_neg (by rw [hRv]; decide), hrd _ hRv]
    have hbody : elabBody D ms held R body = elabC D ms held (heldRunsAt D (D.heldUnder R)) true
        body := by
      cases R <;> first | exact absurd rfl hR | rfl
    rw [hbody, hb R hR]
    exact elabC_eq_elabW D hrv hc b ms msW hms rd hrd held true body

/-- The design-side hypotheses, for by-name: held parameters run under every computation type. -/
theorem byName_rule (R : Ty) (hR : R ≠ .atom) :
    heldRunsAt byName (byName.heldUnder R) = fun _ => true := by
  funext isRoot
  cases R <;> simp_all [heldRunsAt, Design.heldUnder, byName]

/-- For code value: held parameters never run. -/
theorem codeValue_rule (R : Ty) (_hR : R ≠ .atom) :
    heldRunsAt codeValue (codeValue.heldUnder R) = fun _ => false := by
  funext isRoot
  simp [heldRunsAt, codeValue]

/-- The typed design's decision on translated clauses, for `byType`: run at value positions. -/
theorem byType_rd (kinds : Held) (E : CTy) (hE : E.holds = false) :
    rdOf byType kinds E = fun _ => true := by
  rw [rdOf_byType]; funext x; simp [hE]

/-- For `codeOnly` on translated clauses: never run (every held variable there is `Atom`). -/
theorem codeOnly_rd (ps : List Ty) (pats : List Atom) (E : CTy) (_hE : E.holds = false) :
    rdOf codeOnly (heldTyped (ps.map embedTy) pats) E = fun _ => false := by
  funext x
  simp [rdOf, runsAt, codeOnly, kindOf_embed]

theorem elabFn_embed (D : Design) (hrv : D.rerunValues = false) (hc : D.constructorsRun = true)
    (ha : D.atomBody = false) (b : Bool)
    (hb : ∀ R : Ty, R ≠ .atom → heldRunsAt D (D.heldUnder R) = fun _ => b) (td : TDesign)
    (htd : ∀ (ps : List Ty) (pats : List Atom) (E : CTy), E.holds = false →
      rdOf td (heldTyped (ps.map embedTy) pats) E = fun _ => b)
    (P : SProg) (fn : Fn) :
    elabFn D (modesOf P) fn = elabFnB td (tmodesOf (embedP P)) (embedFn fn) := by
  unfold elabFn elabFnB
  rw [embedFn_params, embedFn_result, embedFn_arity]
  congr 1
  · rw [List.map_map]
    apply List.map_congr_left
    intro T _
    exact (embedTy_check T).symm
  · rw [embedRes_check]
  · show fn.eqns.map _ = fn.eqns.map _
    apply List.map_congr_left
    intro e _
    rw [heldNames_embed]
    congr 1
    unfold bodyB elabV
    exact elabBody_eq D hrv hc ha b hb (modesOf P) _ (modesMatch_embed P) _
      (htd fn.params e.1) _ fn.result (embedRes fn.result) (embedRes_holds_iff fn.result) e.2

theorem elabProg_embed (D : Design) (hrv : D.rerunValues = false)
    (hc : D.constructorsRun = true) (ha : D.atomBody = false) (b : Bool)
    (hb : ∀ R : Ty, R ≠ .atom → heldRunsAt D (D.heldUnder R) = fun _ => b) (td : TDesign)
    (htd : ∀ (ps : List Ty) (pats : List Atom) (E : CTy), E.holds = false →
      rdOf td (heldTyped (ps.map embedTy) pats) E = fun _ => b)
    (P : SProg) : elabProg D P = elabProgB td (embedP P) := by
  unfold elabProg elabProgB
  congr 1
  · unfold embedP
    rw [List.map_map]
    apply List.map_congr_left
    intro fn _
    exact elabFn_embed D hrv hc ha b hb td htd P fn
  · funext q
    show elabQuery D (modesOf P) q = queryB td (embedP P) q
    unfold elabQuery queryB elabV
    have h0 : ∀ E : CTy, E.holds = false → rdOf td [] E = fun _ => b :=
      fun E hE => htd [] [] E hE
    rw [Laws.elabC_heldRun_irrelevant D (modesOf P) (fun _ => false) (fun _ => b) [] false q rfl,
      h0 .undef rfl]
    exact elabC_eq_elabW D hrv hc b (modesOf P) _ (modesMatch_embed P) _ h0 [] false q

/-! ## The two embeddings -/

/-- **By-name is `byType` on the study's programs**: the same core program, for every program. -/
theorem byName_eq_byType (P : SProg) : elabProg byName P = elabProgB byType (embedP P) :=
  elabProg_embed byName rfl rfl rfl true byName_rule byType (fun _ _ E hE => byType_rd _ E hE) P

/-- Every run, at every fuel, and every printed answer list agree. -/
theorem byName_runs_eq (P : SProg) (n : Nat) (q : Atom) :
    Weakening.runQ byName P n q = runB byType (embedP P) n q ∧
      answers byName P n q = answersB byType (embedP P) n q := by
  have hprog := byName_eq_byType P
  have hq : elabQuery byName (modesOf P) q = queryB byType (embedP P) q :=
    congrFun (congrArg Prog.code hprog) q
  have hrun : Weakening.runQ byName P n q = runB byType (embedP P) n q := by
    unfold Weakening.runQ runB
    rw [hprog, hq]
  exact ⟨hrun, by unfold answers answersB; rw [← hrun]; rfl⟩

/-- **Code value is `codeOnly` on the study's programs**: the same core program. -/
theorem codeValue_eq_codeOnly (P : SProg) : elabProg codeValue P = elabProgB codeOnly (embedP P) :=
  elabProg_embed codeValue rfl rfl rfl false codeValue_rule codeOnly
    (fun ps pats E hE => codeOnly_rd ps pats E hE) P

/-- Every run agrees; code value prints a refusal as no answer. -/
theorem codeValue_runs_eq (P : SProg) (n : Nat) (q : Atom) :
    Weakening.runQ codeValue P n q = runB codeOnly (embedP P) n q ∧
      answers codeValue P n q = (runB codeOnly (embedP P) n q).map (observe false) := by
  have hprog := codeValue_eq_codeOnly P
  have hq : elabQuery codeValue (modesOf P) q = queryB codeOnly (embedP P) q :=
    congrFun (congrArg Prog.code hprog) q
  have hrun : Weakening.runQ codeValue P n q = runB codeOnly (embedP P) n q := by
    unfold Weakening.runQ runB
    rw [hprog, hq]
  exact ⟨hrun, by unfold answers; rw [← hrun]; rfl⟩

/-! ## The converse: every typed program, in `byType`, is a by-name program -/

theorem projTy_res_atom (R : CTy) : (projTy R = .atom) ↔ R.holds = true := by
  cases R <;> simp [projTy, CTy.holds]

theorem elabFn_proj (P : TProg) (fn : TFn) :
    elabFnB byType (tmodesOf P) fn = elabFn byName (modesOf (projP P)) (projFn fn) := by
  unfold elabFn elabFnB
  rw [projFn_params, projFn_result, projFn_arity]
  congr 1
  · rw [List.map_map]
    apply List.map_congr_left
    intro T _
    exact (projTy_check T).symm
  · rw [projTy_check]
  · show fn.eqns.map _ = fn.eqns.map _
    apply List.map_congr_left
    intro e _
    rw [heldVars_proj]
    congr 1
    unfold bodyB elabV
    have hRR : fn.result.holds = true ↔ projTy fn.result = .atom := (projTy_res_atom _).symm
    have := elabBody_eq byName rfl rfl rfl true byName_rule (modesOf (projP P))
      (modeView (tmodesOf P)) (modesMatch_proj P) (rdOf byType (heldTyped fn.params e.1))
      (fun E hE => byType_rd _ E hE) (heldNames fn.params e.1) (projTy fn.result) fn.result hRR e.2
    exact this.symm

/-- **Every typed program run in `byType` is the by-name run of its projection**: the same core
program. -/
theorem byType_eq_byName_proj (P : TProg) : elabProgB byType P = elabProg byName (projP P) := by
  unfold elabProg elabProgB
  congr 1
  · unfold projP
    rw [List.map_map]
    apply List.map_congr_left
    intro fn _
    exact elabFn_proj P fn
  · funext q
    show queryB byType P q = elabQuery byName (modesOf (projP P)) q
    unfold elabQuery queryB elabV
    rw [Laws.elabC_heldRun_irrelevant byName (modesOf (projP P)) (fun _ => false) (fun _ => true)
      [] false q rfl, byType_rd [] .undef rfl]
    exact (elabC_eq_elabW byName rfl rfl true (modesOf (projP P)) _ (modesMatch_proj P) _
      (fun E hE => byType_rd _ E hE) [] false q).symm

end ByType

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
