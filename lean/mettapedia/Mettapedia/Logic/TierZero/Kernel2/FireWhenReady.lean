import Mettapedia.Logic.TierZero.Kernel2.Walk

/-!
# The walk that fires a node when its children are ready

The MeTTa kernel `tier0.metta` fires a proof's nodes in any order: a node fires as soon as the
theorems its children name exist. Here (`runF`), rounds go over the nodes; in a round each node that
has not fired and whose children are known fires (`fireAt`), with the kernel's step at a node
(`nodeStep`); rounds repeat until nothing more fires. A node may cite any node, earlier or later.
The proof is accepted (`checkF`) when every node fired and the root names the goal.

Example: the proof `[mp (node 1) (hyp 0), k]` cites its second node from its first; the walk in
order refuses it, this walk fires `k` in the first round and `mp` in the second.

* `checkF_sound`: an accepted proof's goal is derivable (every fired node's conclusion is);
* `checkF_complete`: every derivable goal has a proof this walk accepts: a proof the walk in order
  accepts fires completely in its first round (`runF_of_runT`);
* so `checkF_iff_derivable`: this walk accepts exactly the derivable judgments, as the walk in order
  does (`ChildBound.checkCB_iff_derivable`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Logic.TierZero

variable {R : Type}

/-- The judgment a child names, given the hypotheses and the nodes that have fired. -/
def lookupF (hyps : List Tm) (known : List (Option Tm)) : Kid → Option Tm
  | .hyp i => hyps[i]?
  | .node m => (known[m]?).join

/-- Fire node `i` if it has not fired and its step succeeds. -/
def fireAt (env : Env R) (fr : Frame) (hyps : List Tm) (proof : List (R × List Kid))
    (known : List (Option Tm)) (i : ℕ) : List (Option Tm) :=
  match known[i]?, proof[i]? with
  | some none, some (r, kids) =>
      match nodeStep env fr (lookupF hyps known) r kids with
      | some c => known.set i (some c)
      | none => known
  | _, _ => known

/-- One round over the nodes, in order. -/
def fireRound (env : Env R) (fr : Frame) (hyps : List Tm) (proof : List (R × List Kid))
    (known : List (Option Tm)) : List (Option Tm) :=
  (List.range proof.length).foldl (fireAt env fr hyps proof) known

/-- Rounds until nothing more fires. -/
def fireAll (env : Env R) (fr : Frame) (hyps : List Tm) (proof : List (R × List Kid)) :
    ℕ → List (Option Tm) → List (Option Tm)
  | 0, known => known
  | n + 1, known =>
      let next := fireRound env fr hyps proof known
      if next = known then known else fireAll env fr hyps proof n next

/-- **The walk that fires a node when its children are ready.** -/
def runF (env : Env R) (fr : Frame) (hyps : List Tm) (proof : List (R × List Kid)) : List (Option Tm) :=
  fireAll env fr hyps proof (proof.length + 1) (List.replicate proof.length none)

/-- Accepted: every node fired, and the root names the goal. -/
def checkF (env : Env R) (fr : Frame) (hyps : List Tm) (proof : List (R × List Kid)) (root : Kid)
    (goal : Tm) : Bool :=
  let known := runF env fr hyps proof
  known.all Option.isSome && decide (lookupF hyps known root = some goal)

/-! ## Soundness -/

/-- Every fired node's conclusion is derivable. -/
def FiredDerivable (env : Env R) (fr : Frame) (hyps : List Tm) (known : List (Option Tm)) : Prop :=
  ∀ (i : ℕ) (c : Tm), known[i]? = some (some c) → Derivable (presOf env fr) hyps c

theorem ruleStep_solve {fr : Frame} {ru : Rule} {js : List Tm} {c : Tm} (h : ruleStep fr ru js = some c) :
    ∃ a, ru.solve fr js = some a ∧ ru.concl.inst (substOf a) = some c := by
  unfold ruleStep at h
  unfold Rule.solve
  cases hs : solveKinds fr ru.kinds emptySubst js with
  | none => rw [hs] at h; cases h
  | some τ =>
      rw [hs] at h
      simp only at h ⊢
      cases ha : (List.range ru.nformals).mapM τ with
      | none => rw [ha] at h; cases h
      | some a => rw [ha] at h; exact ⟨a, rfl, h⟩

/-- **A node's step concludes a derivable judgment when its children's judgments are.** -/
theorem nodeStep_derivable {env : Env R} {fr : Frame} (wf : EnvDetermined env) {hyps : List Tm}
    {look : Kid → Option Tm} (hl : ∀ k j, look k = some j → Derivable (presOf env fr) hyps j)
    {r : R} {kids : List Kid} {c : Tm} (h : nodeStep env fr look r kids = some c) :
    Derivable (presOf env fr) hyps c := by
  unfold nodeStep at h
  cases hk : kids.mapM look with
  | none => rw [hk] at h; cases h
  | some js =>
      cases he : env r with
      | none => rw [hk, he] at h; cases h
      | some ru =>
          rw [hk, he] at h
          simp only at h
          obtain ⟨a, hs, hc⟩ := ruleStep_solve h
          obtain ⟨c', hi⟩ := solve_sound fr (wf r ru he) hs
          have hc' := instance_concl hi
          rw [hc] at hc'
          have ecc : c = c' := Option.some.inj hc'
          subst ecc
          have inst : (presOf env fr).inst r a = some (js, c) := by
            show (match env r with
              | some ru => ru.instance fr a
              | none => none) = some (js, c)
            rw [he]; exact hi
          refine Derivable.rule inst fun p mp _ => ?_
          have mj : ∀ j ∈ js, Derivable (presOf env fr) hyps j := by
            intro j m
            have : ∀ (ks : List Kid) (xs : List Tm), ks.mapM look = some xs → ∀ x ∈ xs,
                Derivable (presOf env fr) hyps x := by
              intro ks
              induction ks with
              | nil => intro xs h x m; simp at h; subst h; simp at m
              | cons k ks ih =>
                  intro xs h x m
                  simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
                  cases hk' : look k with
                  | none => simp [hk'] at h
                  | some y =>
                      cases hr : ks.mapM look with
                      | none => simp [hk', hr] at h
                      | some ys =>
                          simp only [hk', hr, Option.bind_some, Option.some.injEq] at h
                          subst h
                          rcases List.mem_cons.mp m with rfl | m
                          · exact hl k _ hk'
                          · exact ih ys hr x m
            exact this kids js hk j m
          exact mj p mp

theorem lookupF_derivable {env : Env R} {fr : Frame} {hyps : List Tm} {known : List (Option Tm)}
    (inv : FiredDerivable env fr hyps known) :
    ∀ k j, lookupF hyps known k = some j → Derivable (presOf env fr) hyps j := by
  intro k j h
  cases k with
  | hyp i => exact Derivable.hyp (List.mem_of_getElem? h)
  | node m =>
      simp only [lookupF] at h
      cases hm : known[m]? with
      | none => rw [hm] at h; cases h
      | some o =>
          rw [hm] at h
          cases o with
          | none => cases h
          | some c => cases h; exact inv m _ hm

theorem fireAt_inv {env : Env R} {fr : Frame} (wf : EnvDetermined env) {hyps : List Tm}
    {proof : List (R × List Kid)} {known : List (Option Tm)} (inv : FiredDerivable env fr hyps known)
    (i : ℕ) : FiredDerivable env fr hyps (fireAt env fr hyps proof known i) := by
  unfold fireAt
  cases hk : known[i]? with
  | none => exact inv
  | some o =>
      cases o with
      | some _ => exact inv
      | none =>
          cases hp : proof[i]? with
          | none => exact inv
          | some x =>
              obtain ⟨r, kids⟩ := x
              simp only
              cases hn : nodeStep env fr (lookupF hyps known) r kids with
              | none => exact inv
              | some c =>
                  intro j c' hj
                  by_cases e : j = i
                  · subst e
                    have lt : j < known.length := (List.getElem?_eq_some_iff.mp hk).1
                    rw [List.getElem?_set_self lt] at hj
                    cases hj
                    exact nodeStep_derivable wf (lookupF_derivable inv) hn
                  · rw [List.getElem?_set_ne (Ne.symm e)] at hj
                    exact inv j c' hj

theorem foldl_inv {env : Env R} {fr : Frame} (wf : EnvDetermined env) {hyps : List Tm}
    {proof : List (R × List Kid)} :
    ∀ (is : List ℕ) (known : List (Option Tm)), FiredDerivable env fr hyps known →
      FiredDerivable env fr hyps (is.foldl (fireAt env fr hyps proof) known)
  | [], _, inv => inv
  | i :: is, _, inv => foldl_inv wf is _ (fireAt_inv wf inv i)

theorem fireAll_inv {env : Env R} {fr : Frame} (wf : EnvDetermined env) {hyps : List Tm}
    {proof : List (R × List Kid)} :
    ∀ (n : ℕ) (known : List (Option Tm)), FiredDerivable env fr hyps known →
      FiredDerivable env fr hyps (fireAll env fr hyps proof n known)
  | 0, _, inv => inv
  | n + 1, known, inv => by
      simp only [fireAll]
      split
      · exact inv
      · exact fireAll_inv wf n _ (foldl_inv wf _ known inv)

/-- **Soundness of the walk that fires when ready.** -/
theorem checkF_sound {env : Env R} {fr : Frame} (wf : EnvDetermined env) {hyps : List Tm}
    {proof : List (R × List Kid)} {root : Kid} {goal : Tm}
    (h : checkF env fr hyps proof root goal = true) : Derivable (presOf env fr) hyps goal := by
  unfold checkF at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have inv : FiredDerivable env fr hyps (runF env fr hyps proof) :=
    fireAll_inv wf _ _ fun i c hi => by simp [List.getElem?_replicate] at hi
  exact lookupF_derivable inv root goal h.2

/-! ## Completeness: a proof in order fires in one round -/

theorem lookupF_agree {hyps out : List Tm} {k : ℕ} {known : List (Option Tm)}
    (hk : ∀ m < k, known[m]? = some (out[m]?)) {kid : Kid} (valid : KidValid hyps.length k kid) :
    lookupF hyps known kid = lookupT hyps out kid := by
  cases kid with
  | hyp i => rfl
  | node m =>
      have lt : m < k := valid
      simp only [lookupF, lookupT, hk m lt, Option.join_some]

theorem mapM_congr_valid {hyps out : List Tm} {k : ℕ} {known : List (Option Tm)}
    (hk : ∀ m < k, known[m]? = some (out[m]?)) :
    ∀ (kids : List Kid), (∀ kid ∈ kids, KidValid hyps.length k kid) →
      kids.mapM (lookupF hyps known) = kids.mapM (lookupT hyps out)
  | [], _ => rfl
  | kid :: kids, valid => by
      simp only [List.mapM_cons, lookupF_agree hk (valid kid List.mem_cons_self),
        mapM_congr_valid hk kids fun x m => valid x (List.mem_cons_of_mem _ m)]

theorem nodeStep_congr_valid {env : Env R} {fr : Frame} {hyps out : List Tm} {k : ℕ}
    {known : List (Option Tm)} (hk : ∀ m < k, known[m]? = some (out[m]?)) {r : R} {kids : List Kid}
    (valid : ∀ kid ∈ kids, KidValid hyps.length k kid) :
    nodeStep env fr (lookupF hyps known) r kids = nodeStep env fr (lookupT hyps out) r kids := by
  unfold nodeStep
  rw [mapM_congr_valid hk kids valid]

/-- The walk in order from `done` (`runT`) laid out as a list: node `i` concludes `out[i]`. -/
theorem runT_out {env : Env R} {fr : Frame} {hyps : List Tm} :
    ∀ (done : List Tm) (proof : List (R × List Kid)) (out : List Tm),
      runT env fr hyps done proof = some out →
        out.length = done.length + proof.length ∧ done <+: out ∧
        ∀ i (x : R × List Kid), proof[i]? = some x →
          nodeStep env fr (lookupT hyps (out.take (done.length + i))) x.1 x.2 = out[done.length + i]?
  | done, [], out, h => by
      simp only [runT, Option.some.injEq] at h
      subst h
      exact ⟨by simp, List.prefix_refl _, fun i x hx => by simp at hx⟩
  | done, (r, kids) :: rest, out, h => by
      simp only [runT] at h
      cases hn : nodeStep env fr (lookupT hyps done) r kids with
      | none => rw [hn] at h; cases h
      | some c =>
          rw [hn] at h
          obtain ⟨len, pre, each⟩ := runT_out (done ++ [c]) rest out h
          have pre' : done <+: out := (List.prefix_append done [c]).trans pre
          refine ⟨by simp at len ⊢; omega, pre', fun i x hx => ?_⟩
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
              subst hx
              obtain ⟨tail, rfl⟩ := pre
              rw [Nat.add_zero, show (done ++ [c] ++ tail).take done.length = done by simp,
                show (done ++ [c] ++ tail)[done.length]? = some c by simp]
              exact hn
          | succ i =>
              simp only [List.getElem?_cons_succ] at hx
              have := each i x hx
              simp only [List.length_append, List.length_singleton] at this
              rwa [show done.length + 1 + i = done.length + (i + 1) by omega] at this

theorem mapM_lookupT_valid {hyps done : List Tm} :
    ∀ {kids : List Kid} {js : List Tm}, kids.mapM (lookupT hyps done) = some js →
      ∀ kid ∈ kids, KidValid hyps.length done.length kid
  | [], _, _, _, m => by simp at m
  | k :: ks, js, h, kid, m => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
      cases hk : lookupT hyps done k with
      | none => simp [hk] at h
      | some j =>
          cases hks : ks.mapM (lookupT hyps done) with
          | none => simp [hk, hks] at h
          | some js' =>
              rcases List.mem_cons.mp m with rfl | m
              · cases kid with
                | hyp i => exact (List.getElem?_eq_some_iff.mp hk).1
                | node n => exact (List.getElem?_eq_some_iff.mp hk).1
              · exact mapM_lookupT_valid hks kid m

theorem nodeStep_valid {env : Env R} {fr : Frame} {hyps done : List Tm} {r : R} {kids : List Kid}
    {c : Tm} (h : nodeStep env fr (lookupT hyps done) r kids = some c) :
    ∀ kid ∈ kids, KidValid hyps.length done.length kid := by
  unfold nodeStep at h
  cases hk : kids.mapM (lookupT hyps done) with
  | none => rw [hk] at h; cases h
  | some js => exact mapM_lookupT_valid hk

/-- **A proof the walk in order accepts fires completely in the first round.** -/
theorem fireRound_of_runT {env : Env R} {fr : Frame} {hyps : List Tm} {proof : List (R × List Kid)}
    {out : List Tm} (h : runT env fr hyps [] proof = some out) :
    fireRound env fr hyps proof (List.replicate proof.length none) = out.map some := by
  obtain ⟨len, -, each⟩ := runT_out [] proof out h
  simp only [List.length_nil, Nat.zero_add] at len each
  have step : ∀ k ≤ proof.length,
      (List.range k).foldl (fireAt env fr hyps proof) (List.replicate proof.length none) =
        (out.take k).map some ++ List.replicate (proof.length - k) none := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro le
        rw [List.range_succ, List.foldl_append, ih (by omega)]
        simp only [List.foldl_cons, List.foldl_nil]
        obtain ⟨x, hx⟩ : ∃ x, proof[k]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have ns := each k x hx
        have ok : out[k]? = some out[k] := List.getElem?_eq_getElem (by omega)
        set known := (out.take k).map some ++ List.replicate (proof.length - k) none with hknown
        have hkk : known[k]? = some none := by
          rw [hknown, List.getElem?_append_right (by simp)]
          simp only [List.length_map, List.length_take, Nat.min_eq_left (show k ≤ out.length by omega),
            Nat.sub_self, List.getElem?_replicate]
          rw [if_pos (by omega)]
        have agree : ∀ m < k, known[m]? = some ((out.take k)[m]?) := by
          intro m lt
          rw [hknown, List.getElem?_append_left (by simp; omega)]
          simp [List.getElem?_map, List.getElem?_take_of_lt lt, List.getElem?_eq_getElem (show m < out.length by omega)]
        have valid := nodeStep_valid (ns.trans ok)
        rw [List.length_take, Nat.min_eq_left (by omega)] at valid
        have ns' : nodeStep env fr (lookupF hyps known) x.1 x.2 = some out[k] := by
          rw [nodeStep_congr_valid agree valid, ns, ok]
        unfold fireAt
        rw [hkk, hx]
        simp only
        rw [ns']
        rw [hknown]
        apply List.ext_getElem?
        intro m
        by_cases e : m = k
        · subst e
          rw [List.getElem?_set_self (by simp; omega), List.getElem?_append_left (by simp; omega)]
          simp [List.getElem?_take_of_lt (Nat.lt_succ_self m), ok]
        · rw [List.getElem?_set_ne (Ne.symm e)]
          by_cases lt : m < k
          · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
            simp [List.getElem?_take_of_lt lt, List.getElem?_take_of_lt (show m < k + 1 by omega)]
          · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
            simp only [List.length_map, List.length_take, List.getElem?_replicate,
              Nat.min_eq_left (show k ≤ out.length by omega), Nat.min_eq_left (show k + 1 ≤ out.length by omega)]
            split <;> split <;> first | rfl | (exfalso; omega)
  have all := step proof.length (le_refl _)
  rw [Nat.sub_self, List.replicate_zero, List.append_nil, List.take_of_length_le (by omega)] at all
  exact all

theorem fireAt_fired {env : Env R} {fr : Frame} {hyps : List Tm} {proof : List (R × List Kid)}
    {known : List (Option Tm)} (fired : ∀ (i : ℕ) (o : Option Tm), known[i]? = some o → o.isSome) (i : ℕ) :
    fireAt env fr hyps proof known i = known := by
  unfold fireAt
  cases hk : known[i]? with
  | none => rfl
  | some o =>
      cases o with
      | some _ => rfl
      | none => exact absurd (fired i none hk) (by simp)

theorem fireRound_fired {env : Env R} {fr : Frame} {hyps : List Tm} {proof : List (R × List Kid)}
    {known : List (Option Tm)} (fired : ∀ (i : ℕ) (o : Option Tm), known[i]? = some o → o.isSome) :
    fireRound env fr hyps proof known = known := by
  unfold fireRound
  generalize List.range proof.length = is
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.foldl_cons, fireAt_fired fired i, ih]

/-- **The walk that fires when ready ends where the walk in order does.** -/
theorem runF_of_runT {env : Env R} {fr : Frame} {hyps : List Tm} {proof : List (R × List Kid)}
    {out : List Tm} (h : runT env fr hyps [] proof = some out) :
    runF env fr hyps proof = out.map some := by
  have round := fireRound_of_runT h
  have fired : ∀ (i : ℕ) (o : Option Tm), (out.map some)[i]? = some o → o.isSome := by
    intro i o hi
    simp only [List.getElem?_map] at hi
    cases hout : out[i]? with
    | none => rw [hout] at hi; cases hi
    | some c => rw [hout] at hi; cases hi; rfl
  unfold runF
  simp only [fireAll]
  rw [round]
  split
  · next e => exact e.symm
  · rename_i ne
    cases hl : proof.length with
    | zero =>
        exfalso
        apply ne
        obtain ⟨len, -, -⟩ := runT_out [] proof out h
        have : out = [] := List.eq_nil_of_length_eq_zero (by simp at len; omega)
        subst this
        simp [hl]
    | succ n => simp only [fireAll, fireRound_fired fired, ↓reduceIte]

/-- **Completeness of the walk that fires when ready.** -/
theorem checkF_complete {env : Env R} {fr : Frame} (wf : EnvDetermined env) {hyps : List Tm} {goal : Tm}
    (d : Derivable (presOf env fr) hyps goal) :
    ∃ (proof : List (R × List Kid)) (root : Kid), checkF env fr hyps proof root goal = true := by
  obtain ⟨pf, rt, acc⟩ := (ChildBound.checkCB_iff_derivable (matcherOf env fr wf) hyps goal).mpr d
  rw [Claim.checkCB_eq_runT env fr wf] at acc
  cases hrun : runT env fr hyps [] pf with
  | none => rw [hrun] at acc; cases acc
  | some out =>
      rw [hrun] at acc
      simp only [decide_eq_true_eq] at acc
      refine ⟨pf, rt, ?_⟩
      unfold checkF
      rw [runF_of_runT hrun]
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map]
      refine ⟨fun o ⟨c, _, e⟩ => by rw [← e]; rfl, ?_⟩
      cases rt with
      | hyp i => exact acc
      | node m =>
          simp only [lookupT] at acc
          simp only [lookupF, List.getElem?_map, acc, Option.map_some, Option.join_some]

/-- **The walk that fires when ready accepts exactly the derivable judgments.** -/
theorem checkF_iff_derivable {env : Env R} {fr : Frame} (wf : EnvDetermined env) (hyps : List Tm)
    (goal : Tm) :
    (∃ (proof : List (R × List Kid)) (root : Kid), checkF env fr hyps proof root goal = true) ↔
      Derivable (presOf env fr) hyps goal :=
  ⟨fun ⟨_, _, h⟩ => checkF_sound wf h, checkF_complete wf⟩

/-! ## Controls -/

namespace FireControls

open Controls

/-- `ax-1` cites node `1`, which comes after it: `|- (ph → ((ph → ph) → ph))`. -/
def forward : List (String × List Kid) := [("ax-1", [.hyp 0, .node 1]), ("wi", [.hyp 0, .hyp 0])]

def forwardGoal : Tm := jd "|-" [wiT ph (wiT (wiT ph ph) ph)]

/-- Positive: the walk that fires when ready accepts it (node `1` fires in the first round, node
`0` in the second). -/
theorem forward_fires : checkF (envOf rules) ⟨1, []⟩ [jd "wff" [ph]] forward (.node 0) forwardGoal = true := by
  decide +kernel

/-- Negative: the walk in order refuses it: node `0` cites a node that has not been walked. -/
theorem forward_in_order_refused : runT (envOf rules) ⟨1, []⟩ [jd "wff" [ph]] [] forward = none := by
  decide +kernel

/-- Negative: a wrong goal is refused by the walk that fires when ready too. -/
theorem forward_wrong_goal :
    checkF (envOf rules) ⟨1, []⟩ [jd "wff" [ph]] forward (.node 0) (jd "|-" [wiT ph ph]) = false := by
  decide +kernel

end FireControls

end Mettapedia.Logic.TierZero.Kernel2
