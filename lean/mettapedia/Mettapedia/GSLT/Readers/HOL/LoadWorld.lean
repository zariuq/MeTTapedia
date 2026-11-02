import Mettapedia.GSLT.Readers.HOL.LoadCorrect

/-!
# The loader's program on the kernel's Lean model

`Load.load`'s messages are the admissions and claims of a kernel-version-2 program. Here they are
sent, in order, to the kernel's Lean model (`Kernel2.Spaces`: `World`, `kernelStep`, `runWorld`),
and after each message the model runs until its mailboxes are empty, as kernel-v2 works through a
program line by line.

* `claimOf`: an emitted claim as the kernel's `Claim`: no formals, dummies, hypotheses or locals;
  the statement, store and nodes the loader made; the root record's node as root.
* `runProgram`: the program on the model, from the empty world.
* `runProgram_sound`: every name the model accepts is a claim the program sent, and when it was
  accepted its conclusion was derivable from the claim's hypotheses (`cbHyps`: judgment hypotheses,
  locals, stored terms) in the presentation of the rules then on the board; those rules are a prefix
  of the final board's rules
  (`Kernel2.kernelStep_accepts_sound`, applied at the step that accepted it).
* `load_accepted_derivable`: for the loader, an accepted name is `hol:r.k` for a root `k` whose
  theorem record HOL Light wrote as `hs ⊢ c`, and the derivable conclusion is the encoded sequent
  `(hol.thm (set H₁ … Hₙ) C)` (`thmT`), with `Hᵢ`, `C` the specification's de Bruijn terms encoded,
  derivable from `(given T)` judgments only (`claimOf_givens`).

A stored term enters a derivation only as `(given T)`, a judgment no rule of `holRules` concludes;
the rules cite it through their `given` premises (a name, a set, a substitution list).

Example: bool.ml's TRUTH is accepted as `hol:r.7`, and its conclusion is
`(hol.thm (set) (hol:const "T" (hol:tyapp "bool")))`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.HOL.Load

open Mettapedia.Languages.OpenTheory
open Mettapedia.Logic.TierZero (Derivable)
open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Logic.TierZero.Adequacy.HOL
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

/-! ## The program as client acts -/

/-- **An emitted claim as the kernel's claim.** -/
def claimOf (co : ClaimOut) : Claim String :=
  ⟨"hol:r." ++ toString co.root, [], [], [], [], [], co.concl, co.cs.terms.toList,
    co.cs.nodes.toList.map (fun x => ⟨x.1, x.2.1, x.2.2⟩), .node ((co.cs.recMemo.get? co.root).getD 0)⟩

/-- A message as what a client does: send an admission, or send a claim. -/
def actOf (st : LState) : Msg → Option (ClientAct String)
  | .admit a => some (.sendAdmission a)
  | .claim i => (st.claimsOut[i]?).map fun co => .sendClaim (claimOf co)

/-- The program as client acts, in order. -/
def actsOf (st : LState) : List (ClientAct String) := st.out.toList.filterMap (actOf st)

/-- One message, then the kernel until its mailboxes are empty (at most `fuel` steps). -/
def sendThenRun (fuel : Nat) (w : World String) (a : ClientAct String) : World String :=
  runWorld fuel (a.apply w)

/-- **The program on the kernel's Lean model**: from the empty world, each message in order. -/
def runProgram (fuel : Nat) (as : List (ClientAct String)) : World String :=
  as.foldl (sendThenRun fuel) World.empty

/-- The claims a list of client acts sends. -/
def sentOf (as : List (ClientAct String)) : List (Claim String) :=
  as.filterMap fun a => match a with
    | .sendClaim c => some c
    | .sendAdmission _ => none

/-- The program run message by message, each claim made as it is sent (no list of acts is kept). -/
def runMessages (fuel : Nat) (st : LState) : World String :=
  st.out.toList.foldl (fun w m => (actOf st m).elim w (sendThenRun fuel w)) World.empty

theorem foldl_filterMap_eq {α β γ : Type} (f : α → Option β) (g : γ → β → γ) :
    ∀ (l : List α) (x : γ), (l.filterMap f).foldl g x = l.foldl (fun y a => (f a).elim y (g y)) x
  | [], _ => rfl
  | a :: l, x => by
      cases h : f a with
      | none =>
          simp only [List.filterMap_cons, h, List.foldl_cons, Option.elim_none]
          exact foldl_filterMap_eq f g l x
      | some b =>
          simp only [List.filterMap_cons, h, List.foldl_cons, Option.elim_some]
          exact foldl_filterMap_eq f g l (g x b)

/-- **Message by message is the program run.** -/
theorem runMessages_eq (fuel : Nat) (st : LState) : runMessages fuel st = runProgram fuel (actsOf st) := by
  simp only [runMessages, runProgram, actsOf]
  exact (foldl_filterMap_eq (actOf st) (sendThenRun fuel) st.out.toList World.empty).symm

/-! ## Kernel steps: what they do to the accepted board, the rules and the mailboxes -/

/-- The claims waiting in a world's mailbox and parked aside. -/
def pending (w : World String) : List (Claim String) := w.W ++ w.K

theorem admit_T (w : World String) (m : Admission String) : (admit w m).T = w.T := by
  cases m <;> simp only [admit] <;> split <;> rfl

theorem admit_rules_prefix (w : World String) (m : Admission String) :
    w.L.rules <+: (admit w m).L.rules := by
  cases m with
  | judgment h n => simp only [admit]; split <;> exact List.prefix_refl _
  | sort s => simp only [admit]; split <;> exact List.prefix_refl _
  | rule r ru => simp only [admit]; split <;> simp

theorem admit_pending (w : World String) (m : Admission String) :
    ∀ c ∈ pending (admit w m), c ∈ pending w := by
  intro c hc
  cases m with
  | judgment h n => simp only [admit] at hc; split at hc <;> exact hc
  | sort s => simp only [admit] at hc; split at hc <;> exact hc
  | rule r ru =>
      simp only [admit] at hc
      split at hc
      · simp only [pending, List.append_nil, List.mem_append] at hc ⊢
        exact hc.symm
      · exact hc

theorem checkClaim_T (w : World String) (c : Claim String) :
    (checkClaim w c).T = w.T ∨ (checkClaim w c).T = w.T ++ [c.id] := by
  unfold checkClaim
  split
  · exact Or.inl rfl
  · split
    · split
      · exact Or.inr rfl
      · exact Or.inr rfl
    · split
      · exact Or.inl rfl
      · exact Or.inl rfl

theorem checkClaim_rules_prefix (w : World String) (c : Claim String) :
    w.L.rules <+: (checkClaim w c).L.rules := by
  unfold checkClaim
  split
  · exact List.prefix_refl _
  · split
    · split
      · simp
      · exact List.prefix_refl _
    · split
      · exact List.prefix_refl _
      · exact List.prefix_refl _

theorem checkClaim_pending (w : World String) (c : Claim String) :
    ∀ d ∈ pending (checkClaim w c), d ∈ pending w ∨ d = c := by
  intro d hd
  unfold checkClaim at hd
  split at hd
  · exact Or.inl hd
  · split at hd
    · split at hd
      · simp only [pending, List.append_nil, List.mem_append] at hd ⊢
        tauto
      · exact Or.inl hd
    · split at hd
      · exact Or.inl hd
      · simp only [pending, List.mem_append, List.mem_singleton] at hd ⊢
        tauto

/-- **What a kernel step does to the accepted board**: nothing, or it adds the name of the claim at
the head of the claims mailbox, when no admission is waiting. -/
theorem kernelStep_T {w w' : World String} (h : kernelStep w = some w') {id : String}
    (hid : id ∈ w'.T) : id ∈ w.T ∨ (w.A = [] ∧ ∃ c rest, w.W = c :: rest ∧ c.id = id) := by
  unfold kernelStep at h
  cases hA : w.A with
  | cons m rest =>
      rw [hA] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [admit_T] at hid
      exact Or.inl hid
  | nil =>
      rw [hA] at h
      cases hW : w.W with
      | nil => rw [hW] at h; cases h
      | cons c rest =>
          rw [hW] at h
          simp only [Option.some.injEq] at h
          subst h
          rcases checkClaim_T { w with A := [], W := rest } c with e | e
          · rw [e] at hid; exact Or.inl hid
          · rw [e] at hid
            rcases List.mem_append.mp hid with h1 | h1
            · exact Or.inl h1
            · exact Or.inr ⟨rfl, c, rest, rfl, (List.mem_singleton.mp h1).symm⟩

theorem kernelStep_rules_prefix {w w' : World String} (h : kernelStep w = some w') :
    w.L.rules <+: w'.L.rules := by
  unfold kernelStep at h
  cases hA : w.A with
  | cons m rest =>
      rw [hA] at h
      simp only [Option.some.injEq] at h
      subst h
      exact admit_rules_prefix { w with A := rest } m
  | nil =>
      rw [hA] at h
      cases hW : w.W with
      | nil => rw [hW] at h; cases h
      | cons c rest =>
          rw [hW] at h
          simp only [Option.some.injEq] at h
          subst h
          exact checkClaim_rules_prefix { w with A := [], W := rest } c

theorem kernelStep_pending {w w' : World String} (h : kernelStep w = some w') :
    ∀ d ∈ pending w', d ∈ pending w := by
  intro d hd
  unfold kernelStep at h
  cases hA : w.A with
  | cons m rest =>
      rw [hA] at h
      simp only [Option.some.injEq] at h
      subst h
      exact admit_pending { w with A := rest } m d hd
  | nil =>
      rw [hA] at h
      cases hW : w.W with
      | nil => rw [hW] at h; cases h
      | cons c rest =>
          rw [hW] at h
          simp only [Option.some.injEq] at h
          subst h
          rcases checkClaim_pending { w with A := [], W := rest } c d hd with h1 | h1
          · simp only [pending, List.mem_append, hW, List.mem_cons] at h1 ⊢
            tauto
          · simp [pending, hW, h1]

/-! ## The invariant of a run -/

/-- **Every name on the accepted board was accepted soundly**: it is a claim of `sent`, and at
some reachable world, whose rules are a prefix of `w`'s, the claim's conclusion was derivable from
its hypotheses, locals and stored terms in the presentation of those rules. -/
def AcceptedSound (sent : List (Claim String)) (w : World String) : Prop :=
  ∀ id ∈ w.T, ∃ c ∈ sent, c.id = id ∧ ∃ w₀ : World String, Reachable w₀ ∧ w₀.L.rules <+: w.L.rules ∧
    ∃ hs g, c.cbHyps = some hs ∧ c.goal = some g ∧ Derivable (presOf w₀.env c.frame) hs g

/-- The invariant: reachable, every pending claim sent, every accepted name accepted soundly. -/
structure RunInv (sent : List (Claim String)) (w : World String) : Prop where
  reach : Reachable w
  pend : ∀ c ∈ pending w, c ∈ sent
  acc : AcceptedSound sent w

theorem kernelStep_inv {sent : List (Claim String)} {w w' : World String} (hw : RunInv sent w)
    (h : kernelStep w = some w') : RunInv sent w' := by
  refine ⟨Reachable.kernel hw.reach h, fun c hc => hw.pend c (kernelStep_pending h c hc), ?_⟩
  intro id hid
  have pre := kernelStep_rules_prefix h
  by_cases old : id ∈ w.T
  · obtain ⟨c, hc, hci, w₀, r₀, p₀, rest⟩ := hw.acc id old
    exact ⟨c, hc, hci, w₀, r₀, p₀.trans pre, rest⟩
  · rcases kernelStep_T h hid with h1 | ⟨hA, c, rest, hW, hci⟩
    · exact absurd h1 old
    · subst hci
      have sent_c : c ∈ sent := hw.pend c (by simp [pending, hW])
      obtain ⟨hs, g, e1, e2, d⟩ :=
        kernelStep_accepts_sound hw.reach h old hid ⟨hA, by simp [hW]⟩
      exact ⟨c, sent_c, rfl, w, hw.reach, pre, hs, g, e1, e2, d⟩

theorem runWorld_inv {sent : List (Claim String)} :
    ∀ (n : Nat) {w : World String}, RunInv sent w → RunInv sent (runWorld n w)
  | 0, _, hw => hw
  | n + 1, w, hw => by
      rw [runWorld]
      cases h : kernelStep w with
      | none => exact hw
      | some w' => exact runWorld_inv n (kernelStep_inv hw h)

theorem acceptedSound_mono {sent sent' : List (Claim String)} (sub : ∀ c ∈ sent, c ∈ sent')
    {w : World String} (h : AcceptedSound sent w) : AcceptedSound sent' w := by
  intro id hid
  obtain ⟨c, hc, rest⟩ := h id hid
  exact ⟨c, sub c hc, rest⟩

theorem apply_inv {sent : List (Claim String)} {w : World String} (hw : RunInv sent w)
    (a : ClientAct String) : RunInv (sent ++ sentOf [a]) (a.apply w) := by
  have sub : ∀ c ∈ sent, c ∈ sent ++ sentOf [a] := fun c hc => List.mem_append_left _ hc
  obtain ⟨eL, eT, -⟩ := client_only_sends a w
  refine ⟨Reachable.client a hw.reach, ?_, ?_⟩
  · intro c hc
    cases a with
    | sendAdmission m => exact sub c (hw.pend c hc)
    | sendClaim d =>
        simp only [ClientAct.apply, pending, List.mem_append, List.mem_singleton] at hc
        rcases hc with (h1 | h1) | h1
        · exact sub c (hw.pend c (by simp [pending, h1]))
        · subst h1; simp [sentOf]
        · exact sub c (hw.pend c (by simp [pending, h1]))
  · intro id hid
    rw [eT] at hid
    obtain ⟨c, hc, hci, w₀, r₀, p₀, rest⟩ := hw.acc id hid
    exact ⟨c, sub c hc, hci, w₀, r₀, by rw [eL]; exact p₀, rest⟩

theorem foldl_inv (fuel : Nat) :
    ∀ (as : List (ClientAct String)) {sent : List (Claim String)} {w : World String}, RunInv sent w →
      RunInv (sent ++ sentOf as) (as.foldl (sendThenRun fuel) w)
  | [], sent, w, hw => by simpa [sentOf] using hw
  | a :: as, sent, w, hw => by
      have h1 := runWorld_inv fuel (apply_inv hw a)
      have h2 := foldl_inv fuel as h1
      have e : sent ++ sentOf [a] ++ sentOf as = sent ++ sentOf (a :: as) := by
        cases a <;> simp [sentOf]
      rw [e] at h2
      exact h2

theorem empty_inv : RunInv [] World.empty :=
  ⟨Reachable.empty, fun c hc => by simp [pending, World.empty] at hc,
    fun id hid => by simp [World.empty] at hid⟩

/-- **Soundness of the program run**: every name the kernel's model accepts is a claim the program
sent; when it was accepted, its conclusion was derivable from its hypotheses, locals and stored
terms in the presentation of the rules then on the board, a prefix of the final board's rules. -/
theorem runProgram_sound (fuel : Nat) (as : List (ClientAct String)) :
    AcceptedSound (sentOf as) (runProgram fuel as) := by
  have h := foldl_inv fuel as empty_inv
  simpa [runProgram] using h.acc

/-! ## The loader's claims on the model -/

theorem sentOf_actsOf (st : LState) :
    ∀ c ∈ sentOf (actsOf st), ∃ co ∈ st.claimsOut.toList, c = claimOf co := by
  intro c hc
  simp only [sentOf, actsOf, List.mem_filterMap] at hc
  obtain ⟨a, ⟨m, -, hm⟩, ha⟩ := hc
  cases m with
  | admit x =>
      simp only [actOf, Option.some.injEq] at hm
      subst hm
      simp at ha
  | claim i =>
      simp only [actOf, Option.map_eq_some_iff] at hm
      obtain ⟨co, hco, rfl⟩ := hm
      simp only [Option.some.injEq] at ha
      subst ha
      exact ⟨co, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hco), rfl⟩

theorem claimOf_frame (co : ClaimOut) : (claimOf co).frame = ⟨0, []⟩ := rfl

/-- **An emitted claim's hypotheses are its stored terms as `(given T)`**: it has no judgment
hypotheses and no locals. -/
theorem claimOf_givens {co : ClaimOut} {gs : List Tm} (h : (claimOf co).cbHyps = some gs) :
    ∀ g ∈ gs, IsGiven g := by
  rw [Claim.cbHyps_eq] at h
  intro g m
  obtain ⟨p, mp, ip⟩ := instAll_mem _ h g m
  simp only [Claim.hypPats, claimOf, judgPats, List.map_nil, List.nil_append, List.mem_map] at mp
  obtain ⟨x, -, rfl⟩ := mp
  rw [inst_givenPat] at ip
  cases hx : x.2.inst (claimOf co).σ with
  | none => rw [hx] at ip; simp at ip
  | some t => rw [hx] at ip; simp only [Option.map_some, Option.some.injEq] at ip; exact ⟨t, ip.symm⟩

theorem claimOf_goal {co : ClaimOut}
    {hs : List SourceTerm} {c : SourceTerm} (h : co.concl = thmPatOf hs c) :
    (claimOf co).goal = some (thmT hs c) := by
  simp only [Claim.goal, claimOf, h]
  exact thmPatOf_inst _ hs c

/-- **The loader's program on the kernel's Lean model**: every name the model accepts is
`hol:r.k` for a root `k` whose theorem record HOL Light wrote as `hs ⊢ c`, and when it was accepted
the encoded sequent `(hol.thm (set H₁ … Hₙ) C)` was derivable in the presentation of the rules then
on the board (the presentation `holRules`, the admitted extensions, earlier claims), a prefix of the
final board's rules, from `(given T)` judgments only (`IsGiven`): the claim's stored terms, which the
rules cite through their `given` premises (names, sets, substitution lists). -/
theorem load_accepted_derivable (steps : Array (Option PTStep))
    (thms : Array (Option (List SourceTerm × SourceTerm))) (named : Nat → Bool)
    (profile : List (String × SourceTerm)) (fuel : Nat) :
    ∀ id ∈ (runProgram fuel (actsOf (load steps thms named profile))).T,
      ∃ (k : Nat) (hs : List SourceTerm) (c : SourceTerm), id = "hol:r." ++ toString k ∧ thms[k]? = some (some (hs, c)) ∧
        ∃ (w₀ : World String) (gs : List Tm), Reachable w₀ ∧
          w₀.L.rules <+: (runProgram fuel (actsOf (load steps thms named profile))).L.rules ∧
          (∀ g ∈ gs, IsGiven g) ∧ Derivable (presOf w₀.env ⟨0, []⟩) gs (thmT hs c) := by
  intro id hid
  obtain ⟨cl, hcl, hid', w₀, r₀, p₀, gs, g, ecb, eg, d⟩ := runProgram_sound fuel _ id hid
  obtain ⟨co, hco, rfl⟩ := sentOf_actsOf _ cl hcl
  obtain ⟨-, hs, c, hth, hconcl⟩ := load_claims steps thms named profile co hco
  rw [claimOf_goal hconcl] at eg
  cases eg
  rw [claimOf_frame] at d
  exact ⟨co.root, hs, c, hid'.symm, hth, w₀, gs, r₀, p₀, claimOf_givens ecb, d⟩

end Mettapedia.GSLT.Readers.HOL.Load
