import Mettapedia.Logic.TierZero.Kernel2.Declared

/-!
# The kernel over five spaces: admissions, claims, and rights

The MeTTa kernel-v2 runs over five spaces; here they are a structure (`World`):

* `L`, the **rules board**: declared judgments, sorts and rules. Clients may read it.
* `T`, the **accepted board**: the ids of accepted claims. Clients may read it.
* `A`, the **admissions mailbox**: `admit-judgment`, `admit-sort`, `admit-rule`. Clients may only
  send to it.
* `W`, the **claims mailbox**. Clients may only send to it.
* `K`, the kernel's **private space**: claims waiting for a rule that has not arrived.

**Rights.** A client act (`ClientAct`) only appends to `A` or `W` (`client_only_sends`). Only a
kernel step (`kernelStep`) writes `L`, `T` or `K`.

**Kernel steps.** An admission is checked (`Board.ruleOk` for a rule) and recorded; a claim is
checked by the kernel on thinned terms (`Claim.verdictR`, equal to `Claim.verdict`). An accepted
claim's id goes to `T`. It also becomes a rule on `L` when its proof passes the declared discipline
(`Claim.declaredB`, file `Declared`): every side condition the proof decides on the claim's own names
is one of the claim's hypotheses, which the rule then checks at every instance. Example (finding F5,
`Examples.f5Honest`): `honest` proves `(ne x y)` from `(set x) (set y)` by deciding `(differ x y)` on
its two fresh names. It is accepted, but as a rule it would also fire where `x = y`, so it stays off
`L`; its twin `honest-d`, with the hypothesis `(differ x y)`, becomes a rule.

**Results.**

* `kernelStep_accepts_sound`: whenever a kernel step accepts a claim, its conclusion is derivable
  from its hypotheses, locals and stored terms in the presentation of the rules then on `L`, in the
  claim's frame;
* `kernelStep_claim_conservative`: a claim step adds no theorems: whatever the board derives after
  it, in any frame, the board before it derives from the same hypotheses, some cited terms, and
  some declared sorts of names fresh for the frame (a claim may always take more dummies);
* `reachable_rules_determined`: every rule on `L` of a reachable world is determined, so the
  presentation of `L` has the kernel's matcher, and `verdictR_complete` applies to it;
  `reachable_rules_noFv`: no rule on `L` mentions a claim's name;
* `client_writes_rules_forgery`: if clients could add rules to `L`, any judgment would be
  accepted; the rights are needed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Logic.TierZero

/-! ## Judgment shapes and the checks of admission -/

/-- The heads no judgment may have: the side conditions' and `given`. -/
def reservedHeads : List String :=
  ["given", "differ", "absent-from", "is", "dv", "union-of", "remove-of", "singleton-of", "image-of", "atom-kind",
    "each"]

/-- The number of elements of a field list. -/
def fieldsLen : Fields Head → ℕ
  | .nil => 0
  | .cons _ _ rest => fieldsLen rest + 1

def patFieldsLen : TreePatFields Head ℕ → ℕ
  | .nil => 0
  | .cons _ _ rest => patFieldsLen rest + 1

/-- The head and arity of a judgment pattern `(H p₁ … pₙ)`. -/
def patShape : Pat → Option (String × ℕ)
  | .node .expr (.cons 0 (.node (.sym h) .nil) rest) => some (h, patFieldsLen rest)
  | _ => none

variable {R : Type}

/-- The rules board. -/
structure Board (R : Type) where
  judgments : List (String × ℕ)
  sorts : List String
  rules : List (R × Rule)

/-- A judgment pattern of a declared judgment. -/
def Board.declared (L : Board R) (p : Pat) : Bool :=
  match patShape p with
  | some hn => decide (hn ∈ L.judgments)
  | none => false

/-- Every judgment premise is of a declared judgment. -/
def Board.premsDeclared (L : Board R) (ps : List Premise) : Bool :=
  ps.all fun p => match p with
    | .judg q => L.declared q
    | .each _ _ q => L.declared q
    | _ => true

/-! ## Opaque values -/

/-- A head that could take a dep formal's value apart: a pattern variable, or the symbol `over`
(MeTTa's dep value is `(over X (Y …))`). -/
def badHead : Pat → Bool
  | .mvar _ => true
  | .node (.sym s) .nil => s == "over"
  | _ => false

/-- The head of an expression's fields is not a bad head. -/
def exprHeadOk : TreePatFields Head ℕ → Bool
  | .nil => true
  | .cons _ h _ => !badHead h

/-- A symbol with arguments is not `over`. -/
def symHeadOk (s : String) : TreePatFields Head ℕ → Bool
  | .nil => true
  | .cons _ _ _ => s != "over"

mutual

/-- **No expression in the pattern is headed by a pattern variable or by `over`**, so a dep
formal's value stays opaque to every rule (kernel-v2's `t0:heads-ok?`). Example: `(ty (all $x $p))`
passes; `(ty ($f $a $b))` and `(ty (over $a $b))` do not. -/
def headsOk : Pat → Bool
  | .mvar _ => true
  | .idx _ => true
  | .node .expr fs => exprHeadOk fs && headsOkF fs
  | .node (.sym s) fs => symHeadOk s fs && headsOkF fs
  | .node _ fs => headsOkF fs

def headsOkF : TreePatFields Head ℕ → Bool
  | .nil => true
  | .cons _ p rest => headsOk p && headsOkF rest

end

/-- The admission checks of a rule: determined, declared judgments, no claim names, opaque heads. -/
def Board.ruleOk (L : Board R) (ru : Rule) : Bool :=
  ru.determinedB && L.declared ru.concl && L.premsDeclared ru.prems &&
    patNoFv ru.concl && ru.prems.all (fun p => p.pats.all patNoFv) &&
    headsOk ru.concl && ru.prems.all (fun p => p.pats.all headsOk)

/-- A claim's statement and stored terms have opaque heads. -/
def Claim.headsOkB (c : Claim R) : Bool :=
  headsOk c.concl && c.hyps.all (fun p => p.pats.all headsOk) && c.terms.all (fun x => headsOk x.2)

/-- The admission checks of a claim's statement on the board: declared judgments and sorts, no
claim name (`Claim.noFvB`), opaque heads (`Claim.headsOkB`), and no list premise among its
hypotheses (its proof could not cite one theorem per element). -/
def Board.claimOk (L : Board R) (c : Claim R) : Bool :=
  L.declared c.concl && L.premsDeclared c.hyps &&
    c.locals.all (fun l => decide (l.1 ∈ L.sorts)) && c.noFvB && c.headsOkB &&
    c.hyps.all (fun p => match p with | .each _ _ _ => false | _ => true)

namespace Claim

/-- Every rule a claim's proof cites is on the table. -/
def rulesPresent (env : Env R) (c : Claim R) : Bool :=
  c.proof.all fun nd => (env nd.rule).isSome

end Claim

/-! ## The five spaces -/

/-- Messages to the admissions mailbox. -/
inductive Admission (R : Type) where
  | judgment (h : String) (n : ℕ)
  | sort (s : String)
  | rule (r : R) (ru : Rule)

/-- **The five spaces.** -/
structure World (R : Type) where
  L : Board R
  T : List R
  A : List (Admission R)
  W : List (Claim R)
  K : List (Claim R)

/-- The empty world. -/
def World.empty : World R := ⟨⟨[], [], []⟩, [], [], [], []⟩

/-- What a client may do: send to a mailbox. -/
inductive ClientAct (R : Type) where
  | sendAdmission (m : Admission R)
  | sendClaim (c : Claim R)

/-- A client act appends to a mailbox. -/
def ClientAct.apply : ClientAct R → World R → World R
  | .sendAdmission m, w => { w with A := w.A ++ [m] }
  | .sendClaim c, w => { w with W := w.W ++ [c] }

/-- **Clients only send**: a client act changes neither board nor the private space. -/
theorem client_only_sends (a : ClientAct R) (w : World R) :
    (a.apply w).L = w.L ∧ (a.apply w).T = w.T ∧ (a.apply w).K = w.K := by
  cases a <;> exact ⟨rfl, rfl, rfl⟩

variable [DecidableEq R]

/-- The rule table on the board. -/
def World.env (w : World R) : Env R := envOf w.L.rules

/-- A name is used by the board: a rule's or an accepted claim's. -/
def World.used (w : World R) (r : R) : Bool := (w.L.rules.lookup r).isSome || decide (r ∈ w.T)

/-- Admit one message. -/
def admit (w : World R) : Admission R → World R
  | .judgment h n =>
      if decide (h ∈ reservedHeads) || decide ((h, n) ∈ w.L.judgments) ||
          w.L.judgments.any (fun x => x.1 == h) then w
      else { w with L := { w.L with judgments := w.L.judgments ++ [(h, n)] } }
  | .sort s =>
      if decide ((s, 1) ∈ w.L.judgments) && !decide (s ∈ w.L.sorts) then
        { w with L := { w.L with sorts := w.L.sorts ++ [s] } }
      else w
  | .rule r ru =>
      if !w.used r && w.L.ruleOk ru then
        { w with L := { w.L with rules := w.L.rules ++ [(r, ru)] }, W := w.K ++ w.W, K := [] }
      else w

/-- Check one claim. -/
def checkClaim (w : World R) (c : Claim R) : World R :=
  if w.used c.id || !w.L.claimOk c then w
  else if c.verdictR w.env then
    if c.declaredB w.env then
      { w with L := { w.L with rules := w.L.rules ++ [(c.id, c.toRule)] }, T := w.T ++ [c.id],
               W := w.K ++ w.W, K := [] }
    else { w with T := w.T ++ [c.id] }
  else if c.rulesPresent w.env then w
  else { w with K := w.K ++ [c] }

/-- **A kernel step**: the next admission, else the next claim. -/
def kernelStep (w : World R) : Option (World R) :=
  match w.A with
  | m :: rest => some (admit { w with A := rest } m)
  | [] =>
      match w.W with
      | c :: rest => some (checkClaim { w with W := rest } c)
      | [] => none

/-- Run the kernel until both mailboxes are empty, at most `fuel` steps. -/
def runWorld : ℕ → World R → World R
  | 0, w => w
  | fuel + 1, w =>
      match kernelStep w with
      | some w' => runWorld fuel w'
      | none => w

/-! ## Soundness of kernel steps -/

/-- A claim the step accepted: its id is new on `T`. -/
theorem checkClaim_accepts {w : World R} {c : Claim R} (h : c.id ∉ w.T)
    (acc : c.id ∈ (checkClaim w c).T) : c.verdictR w.env = true := by
  unfold checkClaim at acc
  by_cases u : (w.used c.id || !w.L.claimOk c) = true
  · rw [if_pos u] at acc; exact absurd acc h
  · rw [if_neg u] at acc
    by_cases v : c.verdictR w.env = true
    · exact v
    · rw [if_neg v] at acc
      by_cases p : c.rulesPresent w.env = true
      · rw [if_pos p] at acc; exact absurd acc h
      · rw [if_neg p] at acc; exact absurd acc h

/-- Every rule on the board is determined. -/
def World.Determined (w : World R) : Prop := EnvDetermined w.env

theorem envOf_append_determined {rs : List (R × Rule)} (h : EnvDetermined (envOf rs)) {r : R}
    {ru : Rule} (hr : ru.determinedB = true) : EnvDetermined (envOf (rs ++ [(r, ru)])) := by
  intro r' ru' e
  simp only [envOf, List.lookup_append] at e
  cases hl : rs.lookup r' with
  | some x =>
      rw [hl] at e
      simp only [Option.some_or, Option.some.injEq] at e
      subst e
      exact h r' x hl
  | none =>
      rw [hl] at e
      simp only [Option.none_or, List.lookup] at e
      split at e
      · simp only [Option.some.injEq] at e; subst e; exact hr
      · cases e

omit [DecidableEq R] in
theorem ruleOk_determined {L : Board R} {ru : Rule} (h : L.ruleOk ru = true) : ru.determinedB = true := by
  unfold Board.ruleOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1

omit [DecidableEq R] in
theorem toRule_determined {c : Claim R} (h : c.wellFormed = true) : c.toRule.determinedB = true := by
  simp only [Claim.wellFormed, Claim.stmtOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.2

theorem admit_determined {w : World R} (hw : w.Determined) (m : Admission R) : (admit w m).Determined := by
  cases m with
  | judgment h n => simp only [admit]; split_ifs <;> exact hw
  | sort s => simp only [admit]; split_ifs <;> exact hw
  | rule r ru =>
      simp only [admit]
      split_ifs with c
      · simp only [Bool.and_eq_true] at c
        exact envOf_append_determined hw (ruleOk_determined c.2)
      · exact hw

omit [DecidableEq R] in
theorem verdictR_wellFormed {env : Env R} {c : Claim R} (h : c.verdictR env = true) : c.wellFormed = true := by
  unfold Claim.verdictR at h
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem checkClaim_determined {w : World R} (hw : w.Determined) (c : Claim R) :
    (checkClaim w c).Determined := by
  unfold checkClaim
  split
  · exact hw
  · split
    · next v =>
        split
        · exact envOf_append_determined hw (toRule_determined (verdictR_wellFormed v))
        · exact hw
    · split
      · exact hw
      · exact hw

theorem kernelStep_determined {w w' : World R} (hw : w.Determined) (h : kernelStep w = some w') :
    w'.Determined := by
  unfold kernelStep at h
  cases hA : w.A with
  | cons m rest =>
      rw [hA] at h; simp only [Option.some.injEq] at h; subst h
      exact admit_determined (w := { w with A := rest }) hw m
  | nil =>
      rw [hA] at h
      cases hW : w.W with
      | cons c rest =>
          rw [hW] at h; simp only [Option.some.injEq] at h; subst h
          exact checkClaim_determined (w := { w with A := [], W := rest }) hw c
      | nil => rw [hW] at h; cases h

/-- Worlds reached by client acts and kernel steps. -/
inductive Reachable : World R → Prop
  | empty : Reachable World.empty
  | client {w : World R} (a : ClientAct R) : Reachable w → Reachable (a.apply w)
  | kernel {w w' : World R} : Reachable w → kernelStep w = some w' → Reachable w'

/-- **Every rule on the board of a reachable world is determined.** -/
theorem reachable_rules_determined {w : World R} (h : Reachable w) : w.Determined := by
  induction h with
  | empty => intro r ru e; simp [World.env, World.empty, envOf] at e
  | client a _ ih => cases a <;> exact ih
  | kernel _ step ih => exact kernelStep_determined ih step

/-- **Soundness of a kernel step**: a claim it accepts has a conclusion derivable from its
hypotheses, locals and stored terms in the presentation of the rules on `L` at that moment. -/
theorem kernelStep_accepts_sound {w w' : World R} (hw : Reachable w) (h : kernelStep w = some w')
    {c : Claim R} (hc : c.id ∉ w.T) (acc : c.id ∈ w'.T) (hW : w.A = [] ∧ w.W.head? = some c) :
    ∃ hs g, c.cbHyps = some hs ∧ c.goal = some g ∧ Derivable (presOf w.env c.frame) hs g := by
  obtain ⟨hA, hW⟩ := hW
  unfold kernelStep at h
  rw [hA] at h
  cases hWc : w.W with
  | nil => rw [hWc] at hW; cases hW
  | cons c' rest =>
      rw [hWc] at hW h
      simp only [List.head?_cons, Option.some.injEq] at hW
      subst hW
      simp only [Option.some.injEq] at h
      subst h
      have v := checkClaim_accepts (w := { w with A := [], W := rest }) (c := c') hc acc
      exact verdictR_sound (reachable_rules_determined hw) v

/-! ## No claim names on the board -/

theorem envOf_append_noFv {rs : List (R × Rule)} (h : EnvNoFv (envOf rs)) {r : R} {ru : Rule}
    (hr : RuleNoFv ru) : EnvNoFv (envOf (rs ++ [(r, ru)])) := by
  intro r' ru' e
  simp only [envOf, List.lookup_append] at e
  cases hl : rs.lookup r' with
  | some x =>
      rw [hl] at e
      simp only [Option.some_or, Option.some.injEq] at e
      subst e
      exact h r' x hl
  | none =>
      rw [hl] at e
      simp only [Option.none_or, List.lookup] at e
      split at e
      · simp only [Option.some.injEq] at e; subst e; exact hr
      · cases e

omit [DecidableEq R] in
theorem ruleOk_noFv {L : Board R} {ru : Rule} (h : L.ruleOk ru = true) : RuleNoFv ru := by
  unfold Board.ruleOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1.2, h.1.1.1.2⟩

omit [DecidableEq R] in
theorem claimOk_noFv {L : Board R} {c : Claim R} (h : L.claimOk c = true) : c.noFvB = true := by
  unfold Board.claimOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

omit [DecidableEq R] in
theorem claimOk_sorts {L : Board R} {c : Claim R} (h : L.claimOk c = true) :
    ∀ l ∈ c.locals, l.1 ∈ L.sorts := by
  unfold Board.claimOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

omit [DecidableEq R] in
theorem toRule_noFv {c : Claim R} (h : c.noFvB = true) : RuleNoFv c.toRule := by
  simp only [Claim.noFvB, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨fun p mp q mq => h.1.1.2 p mp q mq, h.1.1.1⟩

theorem admit_noFv {w : World R} (hw : EnvNoFv w.env) (m : Admission R) : EnvNoFv (admit w m).env := by
  cases m with
  | judgment h n => simp only [admit]; split_ifs <;> exact hw
  | sort s => simp only [admit]; split_ifs <;> exact hw
  | rule r ru =>
      simp only [admit]
      split_ifs with c
      · simp only [Bool.and_eq_true] at c
        exact envOf_append_noFv hw (ruleOk_noFv c.2)
      · exact hw

theorem envOf_append_fresh {rs : List (R × Rule)} {r0 : R} (h : rs.lookup r0 = none) (ru0 : Rule) :
    envOf (rs ++ [(r0, ru0)]) = extendEnv (envOf rs) r0 ru0 := by
  funext r
  simp only [envOf, extendEnv, List.lookup_append]
  by_cases e : r = r0
  · subst e; simp [h, List.lookup]
  · have b : (r == r0) = false := beq_false_of_ne e
    simp only [List.lookup, b, if_neg e]
    cases List.lookup r rs <;> rfl

/-- **What a claim step does to the rules board**: nothing, or it adds the claim's rule under a
fresh name, after the claim passed the statement checks, the verdict and the declared discipline. -/
theorem checkClaim_env (w : World R) (c : Claim R) :
    (checkClaim w c).env = w.env ∨
      ((checkClaim w c).env = extendEnv w.env c.id c.toRule ∧ w.L.claimOk c = true ∧
        c.verdictR w.env = true ∧ c.declaredB w.env = true) := by
  unfold checkClaim
  split
  · exact Or.inl rfl
  · next u =>
      split
      · next v =>
          split
          · next d =>
              have lk : w.L.rules.lookup c.id = none := by
                cases hl : w.L.rules.lookup c.id with
                | none => rfl
                | some _ => simp [World.used, hl] at u
              have ok : w.L.claimOk c = true := by
                cases hc : w.L.claimOk c with
                | true => rfl
                | false => simp [hc] at u
              exact Or.inr ⟨envOf_append_fresh lk c.toRule, ok, v, d⟩
          · exact Or.inl rfl
      · split
        · exact Or.inl rfl
        · exact Or.inl rfl

theorem checkClaim_noFv {w : World R} (hw : EnvNoFv w.env) (c : Claim R) : EnvNoFv (checkClaim w c).env := by
  rcases checkClaim_env w c with e | ⟨e, ok, -, -⟩
  · rw [e]; exact hw
  · rw [e]
    intro r ru h
    simp only [extendEnv] at h
    split_ifs at h
    · simp only [Option.some.injEq] at h; subst h; exact toRule_noFv (claimOk_noFv ok)
    · exact hw r ru h

theorem kernelStep_noFv {w w' : World R} (hw : EnvNoFv w.env) (h : kernelStep w = some w') :
    EnvNoFv w'.env := by
  unfold kernelStep at h
  cases hA : w.A with
  | cons m rest =>
      rw [hA] at h; simp only [Option.some.injEq] at h; subst h
      exact admit_noFv (w := { w with A := rest }) hw m
  | nil =>
      rw [hA] at h
      cases hW : w.W with
      | cons c rest =>
          rw [hW] at h; simp only [Option.some.injEq] at h; subst h
          exact checkClaim_noFv (w := { w with A := [], W := rest }) hw c
      | nil => rw [hW] at h; cases h

/-- **No rule on the board of a reachable world mentions a claim's name.** -/
theorem reachable_rules_noFv {w : World R} (h : Reachable w) : EnvNoFv w.env := by
  induction h with
  | empty => intro r ru e; simp [World.env, World.empty, envOf] at e
  | client a _ ih => cases a <;> exact ih
  | kernel _ step ih => exact kernelStep_noFv ih step

/-! ## A claim step adds no theorems -/

/-- **A claim step adds no theorems**: whatever the board derives after a claim step, in any frame,
the board before it derives from the same hypotheses, some cited terms, and some declared sorts of
names fresh for the frame. Admission steps do add theorems: that is what admitting a rule is for. -/
theorem kernelStep_claim_conservative {w w' : World R} (hw : Reachable w) (h : kernelStep w = some w')
    (hA : w.A = []) {fr : Frame} {hyps : List Tm} {j : Tm} (d : Derivable (presOf w'.env fr) hyps j) :
    ∃ gs : List Tm, (∀ g ∈ gs, IsGiven g ∨ IsLocalFact w.L.sorts fr g) ∧
      Derivable (presOf w.env fr) (hyps ++ gs) j := by
  unfold kernelStep at h
  rw [hA] at h
  cases hW : w.W with
  | nil => rw [hW] at h; cases h
  | cons c rest =>
      rw [hW] at h
      simp only [Option.some.injEq] at h
      subst h
      rcases checkClaim_env { w with A := [], W := rest } c with e | ⟨e, ok, v, disc⟩
      · rw [e] at d
        exact ⟨[], by simp, derivable_mono d fun k mk => List.mem_append_left _ mk⟩
      · rw [e] at d
        rw [Claim.verdictR_eq_verdictT] at v
        obtain ⟨gs, G, d'⟩ := derived_conservative w.env (reachable_rules_determined hw)
          (reachable_rules_noFv hw) v disc (claimOk_noFv ok) d
        refine ⟨gs, fun g m => ?_, d'⟩
        rcases G g m with g1 | ⟨s, ms, rest⟩
        · exact Or.inl g1
        · refine Or.inr ⟨s, ?_, rest⟩
          obtain ⟨l, ml, rfl⟩ := List.mem_map.mp ms
          have sorts := claimOk_sorts ok
          exact sorts l ml

/-! ## The rights are needed -/

/-- Steps if clients could also write rules to the board. -/
inductive LooseStep : World R → World R → Prop
  | kernel {w w' : World R} : kernelStep w = some w' → LooseStep w w'
  | client (a : ClientAct R) (w : World R) : LooseStep w (a.apply w)
  | writeRule (w : World R) (r : R) (ru : Rule) :
      LooseStep w { w with L := { w.L with rules := w.L.rules ++ [(r, ru)] } }

/-- **The forgery**: a client that may write rules makes any judgment a theorem of the board's
presentation, with a one-node proof. -/
theorem client_writes_rules_forgery (w : World R) (r : R) (hr : w.L.rules.lookup r = none)
    (fr : Frame) (goal : Pat) (g : Tm) (hg : goal.inst (substOf []) = some g) :
    ∃ w', LooseStep w w' ∧ Derivable (presOf w'.env fr) [] g := by
  refine ⟨_, LooseStep.writeRule w r ⟨0, [], goal⟩, ?_⟩
  have look : envOf (w.L.rules ++ [(r, ⟨0, [], goal⟩)]) r = some ⟨0, [], goal⟩ := by
    simp [envOf, List.lookup_append, hr]
  have inst : (presOf (envOf (w.L.rules ++ [(r, ⟨0, [], goal⟩)])) fr).inst r [] = some ([], g) := by
    simp only [presOf, look]
    simp [Rule.instance, instKinds, Rule.kinds, hg]
  exact Derivable.rule inst (fun p mem => by simp at mem)

end Mettapedia.Logic.TierZero.Kernel2
