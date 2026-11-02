import Mettapedia.Logic.TierZero.Kernel2.Rules

/-!
# Claims: what a client submits, how the kernel reads it, and its verdict

A **claim** is the MeTTa kernel's message
`(claim ID ROOT FORMALS DUMMIES HYPS LOCALS DVL CONCLUSION TERMS PROOF)`, here with its statement
written as patterns over the claim's variables (MeTTa's `$variables`): formals `0 … n-1` (they
become the rule's formals when the claim is accepted), then dummies `n … n+m-1`.

**Freshening.** While the claim is checked, variable `k` takes a value by its kind
(`FormalKind.value`):

* `name`: the fresh name `fv k` (MeTTa's fresh name); example: `ph` of `id`;
* `scope`: also the fresh name `fv k`, a variable others may depend on (MM0's bound variables);
  it is a name and not a bound variable `idx`, so a binder a rule puts around it never captures it
  (finding F6, `Examples.capture`);
* `dep ds`: the fresh name `fv k` over the names of the scope variables `ds` (MM0's regular
  variable with its dependencies; MeTTa's `(over X (Y …))`): the names in a term are its MM0
  support.

**Reading the claim** (`Claim.cbHyps`, `Claim.translate`): its judgment hypotheses become the
theorems `(hyp i)`; a hypothesis that is a side condition or a `(given X)` is no theorem (F2); each
local `(SORT k)` is the theorem `(local i)`; each stored term `T` is the hypothesis `(given T)`,
cited as `(term TID)`; a node cites earlier nodes by name. The kernel translates these into
`ChildBound`'s children (`Kid.hyp`, `Kid.node`), refusing a citation of a non-judgment hypothesis, of
an absent term, or of a later or unknown node.

**Well-formedness** (`Claim.wellFormed`, the admission checks of kernel-v2's `$c2`): the statement
mentions formals only; its hypotheses determine its formals in order (F1, `Rule.determinedB`); each
local names a dummy; each local distinct pair involves a dummy; stored terms mention claim variables
only; term ids and node names are each used once (F4).

**The verdict** (`Claim.verdict`) is `ChildBound.checkCB` on the translation.

* `verdict_sound`: an accepted claim's conclusion is derivable from its hypotheses, locals and
  stored terms in the presentation of the rules, in the claim's frame.
* `verdict_complete`: every derivable conclusion of a well-formed claim is accepted with some proof.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Logic.TierZero

/-! ## Positions in lists -/

/-- The position of `x` in a list. -/
def findPos (x : ℕ) : List ℕ → Option ℕ
  | [] => none
  | y :: ys => if y = x then some 0 else (findPos x ys).map (· + 1)

theorem findPos_spec (x : ℕ) : ∀ {l : List ℕ} {p : ℕ}, findPos x l = some p → l[p]? = some x
  | [], _, h => by simp [findPos] at h
  | y :: ys, p, h => by
      simp only [findPos] at h
      by_cases e : y = x
      · rw [if_pos e] at h; cases h; simp [e]
      · rw [if_neg e] at h
        cases hf : findPos x ys with
        | none => rw [hf] at h; cases h
        | some q =>
            rw [hf] at h; cases h
            simpa using findPos_spec x hf

theorem findPos_of_nodup : ∀ {l : List ℕ} (_ : l.Nodup) {p : ℕ} {x : ℕ}, l[p]? = some x →
    findPos x l = some p
  | [], _, _, _, h => by simp at h
  | y :: ys, nd, p, x, h => by
      obtain ⟨notIn, nd'⟩ := List.nodup_cons.mp nd
      cases p with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h; simp [findPos]
      | succ q =>
          simp only [List.getElem?_cons_succ] at h
          have ne : y ≠ x := fun e => notIn (by rw [e]; exact List.mem_of_getElem? h)
          simp [findPos, ne, findPos_of_nodup nd' h]

theorem findPos_range {k n : ℕ} (lt : n < k) : findPos n (List.range k) = some n :=
  findPos_of_nodup List.nodup_range (by simp [List.getElem?_range lt])

/-! ## Claims -/

/-- How a claim's variable is freshened while the claim is checked. -/
inductive FormalKind where
  /-- A fresh name. -/
  | name
  /-- A scope variable. -/
  | scope
  /-- A fresh name over the scope variables `ds`. -/
  | dep (ds : List ℕ)
  deriving DecidableEq, Repr

/-- The value of variable `k` of a kind while the claim is checked. -/
def FormalKind.value : FormalKind → ℕ → Tm
  | .name, k => fvar k
  | .scope, k => fvar k
  | .dep ds, k => fvar k ds

/-- A child, as a claim writes it. -/
inductive CKid where
  | hyp (i : ℕ)
  | loc (i : ℕ)
  | term (tid : ℕ)
  | node (n : ℕ)
  deriving DecidableEq, Repr

/-- A proof node as a claim writes it: its name, its rule and its children. -/
structure CProofNode (R : Type) where
  name : ℕ
  rule : R
  kids : List CKid

/-- A claim. -/
structure Claim (R : Type) where
  id : R
  formals : List FormalKind
  dummies : List FormalKind
  hyps : List Premise
  /-- Each local `(SORT k)`: a sort name and a dummy variable. -/
  locals : List (String × ℕ)
  dvl : List (Pat × Pat)
  concl : Pat
  /-- The term store: ids and trees. -/
  terms : List (ℕ × Pat)
  proof : List (CProofNode R)
  root : CKid

namespace Claim

variable {R : Type}

/-- The number of formals. -/
def nformals (c : Claim R) : ℕ := c.formals.length

/-- The number of variables, formals and dummies. -/
def nvars (c : Claim R) : ℕ := c.formals.length + c.dummies.length

/-- The values of the claim's variables while it is checked. -/
def vals (c : Claim R) : List Tm := (c.formals ++ c.dummies).mapIdx fun k κ => κ.value k

/-- The freshening substitution. -/
def σ (c : Claim R) : Subst ℕ Tm := substOf c.vals

end Claim

/-- The pattern of a judgment premise. -/
def Premise.judgPat? : Premise → Option Pat
  | .judg p => some p
  | _ => none

/-- The judgment hypotheses' patterns. -/
def judgPats : List Premise → List Pat
  | [] => []
  | p :: ps => match p.judgPat? with
      | some q => q :: judgPats ps
      | none => judgPats ps

/-- The positions of the judgment hypotheses, counted from `s`. -/
def judgPositionsFrom (s : ℕ) : List Premise → List ℕ
  | [] => []
  | p :: ps => match p.judgPat? with
      | some _ => s :: judgPositionsFrom (s + 1) ps
      | none => judgPositionsFrom (s + 1) ps

/-- The positions of the judgment hypotheses. -/
def judgPositions (ps : List Premise) : List ℕ := judgPositionsFrom 0 ps

theorem length_judgPositionsFrom (s : ℕ) :
    ∀ ps : List Premise, (judgPositionsFrom s ps).length = (judgPats ps).length
  | [] => rfl
  | p :: ps => by
      cases h : p.judgPat? <;> simp [judgPositionsFrom, judgPats, h, length_judgPositionsFrom (s + 1) ps]

theorem ge_of_mem_judgPositionsFrom :
    ∀ (s : ℕ) (ps : List Premise) (x : ℕ), x ∈ judgPositionsFrom s ps → s ≤ x
  | _, [], _, h => by simp [judgPositionsFrom] at h
  | s, p :: ps, x, h => by
      cases hp : p.judgPat? with
      | none =>
          simp only [judgPositionsFrom, hp] at h
          have := ge_of_mem_judgPositionsFrom (s + 1) ps x h; omega
      | some _ =>
          simp only [judgPositionsFrom, hp, List.mem_cons] at h
          rcases h with rfl | h
          · exact le_refl _
          · have := ge_of_mem_judgPositionsFrom (s + 1) ps x h; omega

theorem nodup_judgPositionsFrom : ∀ (s : ℕ) (ps : List Premise), (judgPositionsFrom s ps).Nodup
  | _, [] => List.nodup_nil
  | s, p :: ps => by
      cases hp : p.judgPat? with
      | none => simpa [judgPositionsFrom, hp] using nodup_judgPositionsFrom (s + 1) ps
      | some _ =>
          simp only [judgPositionsFrom, hp]
          refine List.nodup_cons.mpr ⟨fun m => ?_, nodup_judgPositionsFrom (s + 1) ps⟩
          have := ge_of_mem_judgPositionsFrom (s + 1) ps s m; omega

namespace Claim

variable {R : Type}

/-- The judgment of a local `(SORT k)`. -/
def localJudgment (c : Claim R) (l : String × ℕ) : Option Tm := (c.vals[l.2]?).map fun v => jd l.1 [v]

/-- **The hypotheses the claim's proof may cite**: its judgment hypotheses, its locals, and
`(given T)` for each stored term, in this order. -/
def cbHyps (c : Claim R) : Option (List Tm) := do
  let hj ← (judgPats c.hyps).mapM fun p => p.inst c.σ
  let hl ← c.locals.mapM c.localJudgment
  let hg ← c.terms.mapM fun x => (x.2.inst c.σ).map givenTm
  pure (hj ++ hl ++ hg)

/-- The claim's goal. -/
def goal (c : Claim R) : Option Tm := c.concl.inst c.σ

/-- The distinct pairs a premise declares. -/
def declaredBy (σ : Subst ℕ Tm) : Premise → Option (Tm × Tm)
  | .dv x y => match x.inst σ, y.inst σ with
      | some a, some b => some (a, b)
      | _, _ => none
  | _ => none

/-- The claim's frame: its variables, and the distinct pairs its hypotheses and local pairs
declare. -/
def frame (c : Claim R) : Frame :=
  ⟨c.nvars, c.hyps.filterMap (declaredBy c.σ) ++
    c.dvl.filterMap fun pq => match pq.1.inst c.σ, pq.2.inst c.σ with
      | some a, some b => some (a, b)
      | _, _ => none⟩

/-- The number of judgment hypotheses and of locals. -/
def nJ (c : Claim R) : ℕ := (judgPats c.hyps).length
def nL (c : Claim R) : ℕ := c.locals.length

/-- Translate a child: `names` are the names of the earlier nodes. -/
def translateKid (c : Claim R) (names : List ℕ) : CKid → Option Kid
  | .hyp i => (findPos i (judgPositions c.hyps)).map Kid.hyp
  | .loc i => if i < c.nL then some (.hyp (c.nJ + i)) else none
  | .term tid => (findPos tid (c.terms.map Prod.fst)).map fun p => .hyp (c.nJ + c.nL + p)
  | .node n => (findPos n names).map Kid.node

/-- Translate the proof, node by node. -/
def translateProof (c : Claim R) : List (CProofNode R) → List ℕ → Option (List (R × List Kid))
  | [], _ => some []
  | nd :: rest, names =>
      match nd.kids.mapM (c.translateKid names), c.translateProof rest (names ++ [nd.name]) with
      | some ks, some more => some ((nd.rule, ks) :: more)
      | _, _ => none

/-- Translate the proof and its root. -/
def translate (c : Claim R) : Option (List (R × List Kid) × Kid) :=
  match c.translateProof c.proof [], c.translateKid (c.proof.map CProofNode.name) c.root with
  | some pf, some rt => some (pf, rt)
  | _, _ => none

/-- The rule an accepted claim becomes. -/
def toRule (c : Claim R) : Rule := ⟨c.nformals, c.hyps, c.concl⟩

/-- The variables a list of premises mentions. -/
def premsVars (ps : List Premise) : Finset ℕ := kindsVars (ps.map Premise.kind)

/-- A dummy variable. -/
def isDummy (c : Claim R) (k : ℕ) : Bool := decide (c.nformals ≤ k) && decide (k < c.nvars)

/-- A pattern that is a dummy variable. -/
def patIsDummy (c : Claim R) : Pat → Bool
  | .mvar k => c.isDummy k
  | _ => false

/-- The kind of a variable. -/
def kindOf (c : Claim R) (k : ℕ) : Option FormalKind := (c.formals ++ c.dummies)[k]?

/-- A kind's dependencies are scope variables of the claim. -/
def kindOk (c : Claim R) : FormalKind → Bool
  | .dep ds => ds.all fun d => c.kindOf d == some .scope
  | _ => true

/-- **The admission checks of a claim.** -/
def stmtOk (c : Claim R) : Bool :=
  decide (c.terms.map Prod.fst).Nodup &&
    decide (premsVars c.hyps ⊆ Finset.range c.nformals) &&
    decide (c.concl.vars ⊆ Finset.range c.nformals) &&
    c.toRule.determinedB &&
    c.locals.all (fun l => c.isDummy l.2) &&
    c.dvl.all (fun pq => c.patIsDummy pq.1 || c.patIsDummy pq.2) &&
    c.terms.all (fun x => decide (x.2.vars ⊆ Finset.range c.nvars)) &&
    (c.formals ++ c.dummies).all c.kindOk

/-- **The admission checks of a claim**: its statement checks, and node names used once. -/
def wellFormed (c : Claim R) : Bool :=
  c.stmtOk && decide (c.proof.map CProofNode.name).Nodup

theorem tids_nodup {c : Claim R} (h : c.stmtOk = true) : (c.terms.map Prod.fst).Nodup := by
  simp only [stmtOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1

/-- **The verdict on a claim**: well-formed, and its translation is accepted by the
children-bound kernel in the claim's frame. -/
def verdict (env : Env R) (wf : EnvDetermined env) (c : Claim R) : Bool :=
  c.wellFormed &&
    match c.cbHyps, c.goal, c.translate with
    | some hs, some g, some (pf, rt) => ChildBound.checkCB (matcherOf env c.frame wf) hs pf rt g
    | _, _, _ => false

end Claim

/-! ## Soundness -/

/-- **Soundness of the verdict**: an accepted claim's conclusion is derivable from its hypotheses,
locals and stored terms, in the presentation of the rules in the claim's frame. -/
theorem verdict_sound {R : Type} {env : Env R} {wf : EnvDetermined env} {c : Claim R}
    (h : c.verdict env wf = true) :
    ∃ hs g, c.cbHyps = some hs ∧ c.goal = some g ∧ Derivable (presOf env c.frame) hs g := by
  simp only [Claim.verdict, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  cases hh : c.cbHyps with
  | none => simp [hh] at h
  | some hs =>
      cases hg : c.goal with
      | none => simp [hh, hg] at h
      | some g =>
          cases ht : c.translate with
          | none => simp [hh, hg, ht] at h
          | some pr =>
              obtain ⟨pf, rt⟩ := pr
              simp only [hh, hg, ht] at h
              exact ⟨hs, g, rfl, rfl, ChildBound.checkCB_sound _ h⟩

/-! ## Completeness: writing any accepted children-bound proof as a claim proof -/

section Completeness

variable {P : Presentation.{0}} [DecidableEq P.J]

/-- A child is valid for `nh` hypotheses and `k` earlier nodes. -/
def KidValid (nh k : ℕ) : Kid → Prop
  | .hyp i => i < nh
  | .node n => n < k

omit [DecidableEq P.J] in
theorem lookup_valid {hyps done : List P.J} {kid : Kid} {j : P.J}
    (h : lookup hyps done kid = some j) : KidValid hyps.length done.length kid := by
  cases kid with
  | hyp i => exact (List.getElem?_eq_some_iff.mp h).1
  | node n => exact (List.getElem?_eq_some_iff.mp h).1

omit [DecidableEq P.J] in
theorem mapM_lookup_valid {hyps done : List P.J} :
    ∀ {kids : List Kid} {js : List P.J}, kids.mapM (lookup hyps done) = some js →
      ∀ kid ∈ kids, KidValid hyps.length done.length kid
  | [], _, _, _, m => by simp at m
  | k :: ks, js, h, kid, m => by
      simp only [List.mapM_cons] at h
      cases hk : lookup hyps done k with
      | none => simp [hk] at h
      | some j =>
          cases hks : ks.mapM (lookup hyps done) with
          | none => simp [hk, hks] at h
          | some js' =>
              rcases List.mem_cons.mp m with rfl | m
              · exact lookup_valid hk
              · exact mapM_lookup_valid hks kid m

/-- **The children of an accepted version-2 walk are valid**: each node cites hypotheses that
exist and earlier nodes only, and the walk adds one conclusion per node. -/
theorem runCB_valid (M : ChildBound.Matcher P) (hyps : List P.J) :
    ∀ (done : List P.J) (proof : List (ChildBound.CNode P)) (out : List P.J),
      ChildBound.runCB M hyps done proof = some out →
        out.length = done.length + proof.length ∧
        ∀ i (x : ChildBound.CNode P), proof[i]? = some x →
          ∀ kid ∈ x.2, KidValid hyps.length (done.length + i) kid
  | done, [], out, h => by
      simp only [ChildBound.runCB, Option.some.injEq] at h
      subst h; simp
  | done, (r, kids) :: rest, out, h => by
      simp only [ChildBound.runCB] at h
      cases hk : kids.mapM (lookup hyps done) with
      | none => simp [hk] at h
      | some js =>
          simp only [hk] at h
          cases hs : M.solve r js with
          | none => simp [hs] at h
          | some a =>
              simp only [hs] at h
              cases hi : P.inst r a with
              | none => simp [hi] at h
              | some pc =>
                  obtain ⟨ps, c⟩ := pc
                  simp only [hi] at h
                  by_cases hd : discharge (lookup hyps done) ps kids = true
                  · simp only [hd, ↓reduceIte] at h
                    obtain ⟨len, valid⟩ := runCB_valid M hyps (done ++ [c]) rest out h
                    refine ⟨by simp at len ⊢; omega, ?_⟩
                    intro i x hx kid m
                    cases i with
                    | zero =>
                        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
                        subst hx
                        simpa using mapM_lookup_valid hk kid m
                    | succ i =>
                        simp only [List.getElem?_cons_succ] at hx
                        have := valid i x hx kid m
                        simp only [List.length_append, List.length_singleton] at this
                        rwa [show done.length + 1 + i = done.length + (i + 1) by omega] at this
                  · simp [hd] at h

end Completeness

theorem length_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h; rfl
  | a :: l, l', h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
      cases hf : f a with
      | none => simp [hf] at h
      | some b =>
          cases hl : l.mapM f with
          | none => simp [hf, hl] at h
          | some bs =>
              simp only [hf, hl, Option.bind_some, Option.some.injEq] at h
              subst h
              simp [length_of_mapM hl]

theorem map_snd_zipIdx {α : Type} : ∀ (l : List α) (k : ℕ), (l.zipIdx k).map Prod.snd = List.range' k l.length
  | [], _ => rfl
  | a :: l, k => by simp [List.zipIdx_cons, List.range'_succ, map_snd_zipIdx l (k + 1)]

namespace Claim

variable {R : Type}

/-- Write a version-2 child as a claim child. -/
def backKid (c : Claim R) : Kid → CKid
  | .node n => .node n
  | .hyp p =>
      if p < c.nJ then .hyp (((judgPositions c.hyps)[p]?).getD 0)
      else if p < c.nJ + c.nL then .loc (p - c.nJ)
      else .term (((c.terms.map Prod.fst)[p - c.nJ - c.nL]?).getD 0)

/-- Write a version-2 proof as a claim proof: node `i` is named `i`. -/
def backProof (c : Claim R) (pf : List (R × List Kid)) (k : ℕ) : List (CProofNode R) :=
  (pf.zipIdx k).map fun x => ⟨x.2, x.1.1, x.1.2.map c.backKid⟩

theorem length_cbHyps {c : Claim R} {hs : List Tm} (h : c.cbHyps = some hs) :
    hs.length = c.nJ + c.nL + c.terms.length := by
  simp only [cbHyps, Option.bind_eq_bind, Option.pure_def] at h
  cases h1 : (judgPats c.hyps).mapM fun p => p.inst c.σ with
  | none => simp [h1] at h
  | some hj =>
      cases h2 : c.locals.mapM c.localJudgment with
      | none => simp [h1, h2] at h
      | some hl =>
          cases h3 : c.terms.mapM (fun x => (x.2.inst c.σ).map givenTm) with
          | none => simp [h1, h2, h3] at h
          | some hg =>
              simp only [h1, h2, h3, Option.bind_some, Option.some.injEq] at h
              subst h
              simp only [List.length_append, length_of_mapM h1, length_of_mapM h2,
                length_of_mapM h3, nJ, nL]

theorem translateKid_back (c : Claim R) (tidsNodup : (c.terms.map Prod.fst).Nodup) {nh : ℕ}
    (len : nh = c.nJ + c.nL + c.terms.length) (k : ℕ) {kid : Kid} (valid : KidValid nh k kid) :
    c.translateKid (List.range k) (c.backKid kid) = some kid := by
  cases kid with
  | node n => simp [backKid, translateKid, findPos_range (show n < k from valid)]
  | hyp p =>
      have pl : p < c.nJ + c.nL + c.terms.length := by rw [← len]; exact valid
      by_cases a : p < c.nJ
      · have plen : p < (judgPositions c.hyps).length := by
          rw [judgPositions, length_judgPositionsFrom]; exact a
        have get := List.getElem?_eq_getElem plen
        have nd : (judgPositions c.hyps).Nodup := nodup_judgPositionsFrom 0 _
        simp only [backKid, a, ↓reduceIte, translateKid, get, Option.getD_some,
          findPos_of_nodup nd get, Option.map_some]
      · by_cases b : p < c.nJ + c.nL
        · simp only [backKid, a, b, ↓reduceIte, translateKid, show p - c.nJ < c.nL by omega,
            Option.some.injEq, Kid.hyp.injEq]
          omega
        · have tlen : p - c.nJ - c.nL < (c.terms.map Prod.fst).length := by simp; omega
          have get := List.getElem?_eq_getElem tlen
          simp only [backKid, a, b, ↓reduceIte, translateKid, get, Option.getD_some,
            findPos_of_nodup tidsNodup get, Option.map_some, Option.some.injEq, Kid.hyp.injEq]
          omega

theorem mapM_translateKid_back (c : Claim R) (tidsNodup : (c.terms.map Prod.fst).Nodup) {nh : ℕ}
    (len : nh = c.nJ + c.nL + c.terms.length) (k : ℕ) :
    ∀ (kids : List Kid), (∀ kid ∈ kids, KidValid nh k kid) →
      (kids.map c.backKid).mapM (c.translateKid (List.range k)) = some kids
  | [], _ => rfl
  | kid :: kids, valid => by
      simp only [List.map_cons, List.mapM_cons,
        translateKid_back c tidsNodup len k (valid kid List.mem_cons_self),
        mapM_translateKid_back c tidsNodup len k kids (fun x m => valid x (List.mem_cons_of_mem _ m)),
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem translateProof_back (c : Claim R) (tidsNodup : (c.terms.map Prod.fst).Nodup) {nh : ℕ}
    (len : nh = c.nJ + c.nL + c.terms.length) :
    ∀ (pf : List (R × List Kid)) (k : ℕ),
      (∀ i (x : R × List Kid), pf[i]? = some x → ∀ kid ∈ x.2, KidValid nh (k + i) kid) →
        c.translateProof (c.backProof pf k) (List.range k) = some pf
  | [], _, _ => rfl
  | (r, kids) :: rest, k, valid => by
      have here := mapM_translateKid_back c tidsNodup len k kids
        (fun kid m => by simpa using valid 0 (r, kids) rfl kid m)
      have more := translateProof_back c tidsNodup len rest (k + 1) (fun i x hx kid m => by
        have := valid (i + 1) x (by simpa using hx) kid m
        rwa [show k + (i + 1) = k + 1 + i by omega] at this)
      rw [show List.range (k + 1) = List.range k ++ [k] from List.range_succ] at more
      simp only [backProof, List.zipIdx_cons, List.map_cons, translateProof]
      simp only [backProof] at more
      rw [here, more]

/-- Replacing a claim's proof and root changes nothing else it is read for. -/
theorem withProof_cbHyps (c : Claim R) (p : List (CProofNode R)) (r : CKid) :
    ({ c with proof := p, root := r } : Claim R).cbHyps = c.cbHyps := rfl

theorem withProof_goal (c : Claim R) (p : List (CProofNode R)) (r : CKid) :
    ({ c with proof := p, root := r } : Claim R).goal = c.goal := rfl

theorem withProof_frame (c : Claim R) (p : List (CProofNode R)) (r : CKid) :
    ({ c with proof := p, root := r } : Claim R).frame = c.frame := rfl

theorem withProof_stmtOk (c : Claim R) (p : List (CProofNode R)) (r : CKid) :
    ({ c with proof := p, root := r } : Claim R).stmtOk = c.stmtOk := rfl

theorem withProof_translateProof (c : Claim R) (p : List (CProofNode R)) (r : CKid) :
    ∀ (l : List (CProofNode R)) (names : List ℕ),
      ({ c with proof := p, root := r } : Claim R).translateProof l names = c.translateProof l names
  | [], _ => rfl
  | nd :: rest, names => by
      simp only [translateProof, withProof_translateProof c p r rest]
      rfl

theorem names_backProof (c : Claim R) :
    ∀ (pf : List (R × List Kid)) (k : ℕ), (c.backProof pf k).map CProofNode.name = List.range' k pf.length
  | [], _ => rfl
  | x :: pf, k => by
      simp only [backProof, List.zipIdx_cons, List.map_cons, List.length_cons, List.range'_succ]
      exact congrArg (k :: ·) (names_backProof c pf (k + 1))

theorem withProof_translateKid (c : Claim R) (p : List (CProofNode R)) (r : CKid) :
    ({ c with proof := p, root := r } : Claim R).translateKid = c.translateKid := rfl

end Claim

/-- **Completeness of the verdict**: a claim whose statement passes the admission checks and whose
conclusion is derivable is accepted with some proof and root. -/
theorem verdict_complete {R : Type} {env : Env R} {wf : EnvDetermined env} {c : Claim R}
    (ok : c.stmtOk = true) {hs : List Tm} {g : Tm} (hh : c.cbHyps = some hs)
    (hg : c.goal = some g) (d : Derivable (presOf env c.frame) hs g) :
    ∃ (proof : List (CProofNode R)) (root : CKid),
      ({ c with proof := proof, root := root } : Claim R).verdict env wf = true := by
  obtain ⟨pf, rt, acc⟩ := (ChildBound.checkCB_iff_derivable (matcherOf env c.frame wf) hs g).mpr d
  unfold ChildBound.checkCB at acc
  cases hrun : ChildBound.runCB (matcherOf env c.frame wf) hs [] pf with
  | none => simp [hrun] at acc
  | some out =>
      simp only [hrun, decide_eq_true_eq] at acc
      obtain ⟨len, valid⟩ := runCB_valid (matcherOf env c.frame wf) hs [] pf out hrun
      simp only [List.length_nil, Nat.zero_add] at len valid
      have hlen := Claim.length_cbHyps hh
      have tids := Claim.tids_nodup ok
      refine ⟨c.backProof pf 0, c.backKid rt, ?_⟩
      have names : (c.backProof pf 0).map CProofNode.name = List.range pf.length :=
        (Claim.names_backProof c pf 0).trans (List.range_eq_range' ..).symm
      have trP : c.translateProof (c.backProof pf 0) [] = some pf :=
        Claim.translateProof_back c tids hlen pf 0 (fun i x hx kid m => by
          rw [Nat.zero_add]; exact valid i x hx kid m)
      have rootValid : KidValid hs.length pf.length rt := by
        have := lookup_valid acc; rwa [len] at this
      have trR : c.translateKid (List.range pf.length) (c.backKid rt) = some rt :=
        Claim.translateKid_back c tids hlen pf.length rootValid
      have checked : ChildBound.checkCB (matcherOf env c.frame wf) hs pf rt g = true := by
        simp [ChildBound.checkCB, hrun, acc]
      simp only [Claim.verdict, Claim.wellFormed, Claim.withProof_stmtOk, ok, Bool.true_and,
        Claim.withProof_cbHyps, hh, Claim.withProof_goal, hg, Claim.translate,
        Claim.withProof_translateProof, trP, Claim.withProof_translateKid, names, trR,
        List.nodup_range, decide_true]
      exact checked

end Mettapedia.Logic.TierZero.Kernel2
