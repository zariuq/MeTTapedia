import Mettapedia.GSLT.Readers.HOL.Load

/-!
# What the HOL loader's claims say

`Load.load` turns HOL Light's ProofTrace record into kernel-version-2 claims. This file proves, for
every input:

* `load_claims`: every claim the loader emits is well-formed (`WellFormed`: nodes named in order,
  every child an earlier node or a store entry, store ids distinct and in order, the root a node)
  and states its root's theorem record: its conclusion is `thmPatOf hs c` for the record's
  hypotheses `hs` and conclusion `c`;
* `thmPatOf_eq`, `thmPatOf_inst`: that statement is the closed pattern of the kernel term
  `(hol.thm (set H₁ … Hₙ) C)` with `Hᵢ = encDB (toDB [] hᵢ)` and `C = encDB (toDB [] c)`
  (`HOLEnc.encDB`), and instantiates to exactly that term;
* `encSet_of_check`: when the hypotheses type check (`SourceTerm.check`), the claim's set term stands
  for them, `EncSet (set …) H` with `H` their checked terms (`HOLEnc.EncSet`).

Not proved here: that the partial builders (`tmNode`, `recNode`, …) never fail on HOL Light's
records (they are run; a failure stops the load), and the adequacy of `holRules` itself (the
kernel-in-Lean work, `Adequacy/HOL*`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.HOL.Load

open Mettapedia.Languages.OpenTheory
open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Logic.TierZero.Adequacy.HOL
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

/-! ## The fold keeps every emitted claim good -/

/-- An emitted claim is good: well-formed, and stating its root's theorem record. -/
def GoodClaim (thms : Array (Option (List SourceTerm × SourceTerm))) (co : ClaimOut) : Prop :=
  WellFormed co.root co.cs ∧ ∃ hs c, thms[co.root]? = some (some (hs, c)) ∧ co.concl = thmPatOf hs c

theorem admitRules_claimsOut (st : LState) (rs : List (String × Rule)) :
    (admitRules st rs).claimsOut = st.claimsOut := by
  unfold admitRules
  induction rs generalizing st with
  | nil => rfl
  | cons nr rest ih => simpa using ih _

theorem stop_claimsOut (st : LState) (k : Nat) (why : String) : (stop st k why).claimsOut = st.claimsOut :=
  rfl

theorem admitAxiom_claimsOut (st : LState) (k : Nat) (t : SourceTerm) (p : List (String × SourceTerm)) :
    (admitAxiom st k t p).claimsOut = st.claimsOut := by
  unfold admitAxiom
  dsimp only
  split
  · split <;> simp [admitRules_claimsOut]
  · rfl

theorem defineConst_claimsOut (st : LState) (k : Nat) (t : SourceTerm) (name : String) :
    (defineConst st k t name).claimsOut = st.claimsOut := by
  unfold defineConst
  dsimp only
  repeat' split
  all_goals simp [stop_claimsOut, admitRules_claimsOut]

theorem defineType_claimsOut (st : LState) (k p : Nat) (a r : SourceTerm) (an rn : String)
    (thms : Array (Option (List SourceTerm × SourceTerm))) :
    (defineType st k p a r an rn thms).claimsOut = st.claimsOut := by
  unfold defineType
  dsimp only
  repeat' split
  all_goals simp [stop_claimsOut, admitRules_claimsOut]

theorem typeDefStep_claimsOut (env : Env) (st : LState) (k p : Nat) (t : SourceTerm) (an : String) :
    (typeDefStep env st k p t an).claimsOut = st.claimsOut := by
  unfold typeDefStep
  repeat' split
  all_goals simp [stop_claimsOut, defineType_claimsOut]

/-- At a root the claim step adds one claim, well-formed and stating the root's theorem record, or
nothing. -/
theorem claimStep_cases (env : Env) (st : LState) (k : Nat) :
    (claimStep env st k).claimsOut = st.claimsOut ∨
      ∃ hs c cs, env.thms[k]? = some (some (hs, c)) ∧ wfB k cs = true ∧
        (claimStep env st k).claimsOut = st.claimsOut.push ⟨k, thmPatOf hs c, cs⟩ := by
  unfold claimStep
  split
  · split
    · next hs c hth =>
      dsimp only
      split
      · next cs _ =>
        split
        · next hwf => exact Or.inr ⟨hs, c, cs, hth, hwf, rfl⟩
        · exact Or.inl rfl
      · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem stepRec_cases (env : Env) (st : LState) (k : Nat) :
    (stepRec env st k).claimsOut = st.claimsOut ∨
      ∃ hs c cs, env.thms[k]? = some (some (hs, c)) ∧ wfB k cs = true ∧
        (stepRec env st k).claimsOut = st.claimsOut.push ⟨k, thmPatOf hs c, cs⟩ := by
  unfold stepRec
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  split
  · next s _ =>
    split
    · exact Or.inl rfl
    · cases s with
      | newAxiom t => exact Or.inl (admitAxiom_claimsOut _ _ _ _)
      | newDefinition t name => exact Or.inl (defineConst_claimsOut _ _ _ _)
      | newTypeDefinition p t an => exact Or.inl (typeDefStep_claimsOut _ _ _ _ _ _)
      | _ => exact claimStep_cases env st k
  · exact Or.inl rfl

theorem stepRec_good (env : Env) (st : LState) (k : Nat)
    (h : ∀ co ∈ st.claimsOut.toList, GoodClaim env.thms co) :
    ∀ co ∈ (stepRec env st k).claimsOut.toList, GoodClaim env.thms co := by
  rcases stepRec_cases env st k with heq | ⟨hs, c, cs, hth, hwf, heq⟩
  · rw [heq]; exact h
  · rw [heq]
    intro co hco
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hco
    rcases hco with hco | rfl
    · exact h co hco
    · exact ⟨(wfB_iff k cs).mp hwf, hs, c, hth, rfl⟩

theorem foldl_admitJudgment_claimsOut : ∀ (js : List (String × Nat)) (st : LState),
    (js.foldl admitJudgment st).claimsOut = st.claimsOut
  | [], _ => rfl
  | jn :: js, st => foldl_admitJudgment_claimsOut js (admitJudgment st jn)

theorem initial_claimsOut : initial.claimsOut = #[] := by
  unfold initial
  rw [admitRules_claimsOut, admitRules_claimsOut, foldl_admitJudgment_claimsOut]

theorem foldl_good (env : Env) : ∀ (ks : List Nat) (st : LState),
    (∀ co ∈ st.claimsOut.toList, GoodClaim env.thms co) →
    ∀ co ∈ (ks.foldl (stepRec env) st).claimsOut.toList, GoodClaim env.thms co
  | [], _, h => h
  | k :: ks, st, h => foldl_good env ks _ (stepRec_good env st k h)

/-- **Every claim the loader emits is well-formed and states its root's theorem record.** -/
theorem load_claims (steps : Array (Option PTStep)) (thms : Array (Option (List SourceTerm × SourceTerm)))
    (named : Nat → Bool) (profile : List (String × SourceTerm)) :
    ∀ co ∈ (load steps thms named profile).claimsOut.toList, GoodClaim thms co := by
  unfold load
  exact foldl_good _ _ _ (by simp [initial_claimsOut])

/-! ## The statement is the encoding of the theorem record -/

mutual

theorem patOf_inst (σ : Subst ℕ Tm) : ∀ t : Tm, (patOf t).inst σ = some t
  | .idx n => rfl
  | .node h fs => by simp [patOf, TreePat.inst, patFields_inst σ fs]

theorem patFields_inst (σ : Subst ℕ Tm) : ∀ fs : Fields Head, TreePatFields.inst σ (patFields fs) = some fs
  | .nil => rfl
  | .cons d t rest => by simp [patFields, TreePatFields.inst, patOf_inst σ t, patFields_inst σ rest]

end

theorem patFields_flds : ∀ ts : List Tm, patFields (flds ts) = pflds (ts.map patOf)
  | [] => rfl
  | t :: ts => by simp [flds, pflds, patFields, patFields_flds ts]

theorem patOf_ex (ts : List Tm) : patOf (ex ts) = pex (ts.map patOf) := by
  simp [ex, pex, patOf, patFields_flds]

theorem patOf_sym (s : String) : patOf (sym s) = psym s := rfl

/-- The kernel term a claim states: `(hol.thm (set H₁ … Hₙ) C)`, every part `encDB (toDB [] ·)`. -/
def thmT (hs : List SourceTerm) (c : SourceTerm) : Tm := jd "hol.thm" [setT (hs.map encSrc), encSrc c]

theorem patEnc_eq : patEnc = fun t => patOf (encSrc t) := rfl

/-- **The claim's statement is the closed pattern of the encoded sequent.** -/
theorem thmPatOf_eq (hs : List SourceTerm) (c : SourceTerm) : thmPatOf hs c = patOf (thmT hs c) := by
  simp [thmPatOf, setPatOf, thmJ, pjd, setP, patEnc_eq, thmT, jd, setT, patOf_ex, patOf_sym, List.map_map,
    Function.comp_def]

/-- **The statement instantiates to exactly the encoded sequent**, whatever the substitution: it is
closed. -/
theorem thmPatOf_inst (σ : Subst ℕ Tm) (hs : List SourceTerm) (c : SourceTerm) :
    (thmPatOf hs c).inst σ = some (thmT hs c) := by
  rw [thmPatOf_eq]; exact patOf_inst σ _

/-! ## The hypothesis set stands for the checked hypotheses -/

theorem fieldsAtZero_flds : ∀ ts : List Tm, fieldsAtZero (flds ts) = some ts
  | [] => rfl
  | t :: ts => by simp [flds, fieldsAtZero, fieldsAtZero_flds ts]

theorem setMembers_setT (ms : List Tm) : setMembers (setT ms) = some ms := by
  simp [setT, ex, flds, sym, setMembers, fieldsAtZero_flds]

theorem check_term {h : SourceTerm} {ch : CanonicalTerm} (hc : SourceTerm.check h = some ch) :
    ch.term = h.toDB [] := by
  unfold SourceTerm.check at hc
  dsimp only at hc
  split at hc
  · cases hc; rfl
  · cases hc

theorem encCT_of_check {h : SourceTerm} {ch : CanonicalTerm} (hc : SourceTerm.check h = some ch) :
    encCT ch = encSrc h := by
  simp [encCT, encSrc, check_term hc]

/-- Checking a list of hypotheses: every hypothesis has its checked term in the result and every
result is some hypothesis's. -/
theorem mapM_check_mem : ∀ {hs : List SourceTerm} {chs : List CanonicalTerm},
    hs.mapM SourceTerm.check = some chs →
      (∀ a ∈ hs, ∃ b ∈ chs, SourceTerm.check a = some b) ∧
        (∀ b ∈ chs, ∃ a ∈ hs, SourceTerm.check a = some b)
  | [], chs, h => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h; simp
  | a :: as, chs, h => by
      simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h
      cases ha : SourceTerm.check a with
      | none => simp [ha] at h
      | some b =>
        cases has : as.mapM SourceTerm.check with
        | none => simp [ha, has] at h
        | some bs =>
          simp only [ha, has, Option.bind_some, Option.some.injEq] at h
          subst h
          obtain ⟨ih1, ih2⟩ := mapM_check_mem has
          refine ⟨?_, ?_⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact ⟨b, List.mem_cons_self, ha⟩
            · obtain ⟨y, hy, hxy⟩ := ih1 x hx
              exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact ⟨a, List.mem_cons_self, ha⟩
            · obtain ⟨x, hx, hxy⟩ := ih2 y hy
              exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩

/-- **When the hypotheses type check, the claim's set term stands for them** (`EncSet`): its members
are exactly the encodings of the checked hypotheses. -/
theorem encSet_of_check (hs : List SourceTerm) (chs : List CanonicalTerm)
    (h : hs.mapM SourceTerm.check = some chs) : EncSet (setT (hs.map encSrc)) chs.toFinset := by
  refine ⟨hs.map encSrc, setMembers_setT _, ?_⟩
  intro x
  obtain ⟨m1, m2⟩ := mapM_check_mem h
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, hab⟩ := m1 a ha
    exact ⟨b, List.mem_toFinset.mpr hb, encCT_of_check hab⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hab⟩ := m2 b (List.mem_toFinset.mp hb)
    exact List.mem_map.mpr ⟨a, ha, (encCT_of_check hab).symm⟩

/-- **The loader's claims, in the specification's terms**: every emitted claim is well-formed; its
statement is the closed pattern of `(hol.thm S C)` with `C = encDB` of its root's conclusion and `S`
the set term of the hypotheses, which stands for them (`EncSet`) whenever they type check. -/
theorem load_claims_encode (steps : Array (Option PTStep))
    (thms : Array (Option (List SourceTerm × SourceTerm))) (named : Nat → Bool)
    (profile : List (String × SourceTerm)) :
    ∀ co ∈ (load steps thms named profile).claimsOut.toList,
      WellFormed co.root co.cs ∧ ∃ hs c, thms[co.root]? = some (some (hs, c)) ∧
        co.concl = patOf (jd "hol.thm" [setT (hs.map encSrc), encSrc c]) ∧
        ∀ chs, hs.mapM SourceTerm.check = some chs → EncSet (setT (hs.map encSrc)) chs.toFinset := by
  intro co hco
  obtain ⟨hwf, hs, c, hth, hc⟩ := load_claims steps thms named profile co hco
  exact ⟨hwf, hs, c, hth, hc.trans (thmPatOf_eq hs c), fun chs h => encSet_of_check hs chs h⟩

/-! ## Controls -/

/-- A record term: `T` at `bool`. -/
private def tT : SourceTerm := .const (.mk (Name.global "T") .undefined) (.op (opOf "bool") [])

/-- `⊢ T` is stated as `(hol.thm (set) (hol:const "T" (hol:tyapp "bool")))`. -/
theorem control_truth_statement :
    renderPat (thmPatOf [] tT) = "(hol.thm (set) (hol:const \"T\" (hol:tyapp \"bool\")))" := by
  decide +kernel

/-- `\x. x` and `\y. y` at `bool` are one kernel term: `(bind (hol:tyapp "bool") (bv 0))`. -/
theorem control_alpha :
    renderPat (patEnc (.abs (Name.global "x") (.op (opOf "bool") []) (.var (Name.global "x") (.op (opOf "bool") [])))) =
      renderPat (patEnc (.abs (Name.global "y") (.op (opOf "bool") []) (.var (Name.global "y") (.op (opOf "bool") [])))) ∧
    renderPat (patEnc (.abs (Name.global "x") (.op (opOf "bool") []) (.var (Name.global "x") (.op (opOf "bool") [])))) =
      "(bind (hol:tyapp \"bool\") (bv 0))" := by
  decide +kernel

/-- A free variable of another type is no bound variable: in `\x:bool. x:num`, `x:num` stays free. -/
theorem control_bound_by_name_and_type :
    renderPat (patEnc (.abs (Name.global "x") (.op (opOf "bool") []) (.var (Name.global "x") (.op (opOf "num") [])))) =
      "(bind (hol:tyapp \"bool\") (hol:var \"x\" (hol:tyapp \"num\")))" := by
  decide +kernel

/-- HOL Light's `fun` is the specification's `->` and prints back as `fun`. -/
theorem control_fun_name :
    holKey (holTyOf (.op (opOf "fun") [.op (opOf "bool") [], .op (opOf "bool") []])) =
      "(hol:tyapp \"fun\" (hol:tyapp \"bool\") (hol:tyapp \"bool\"))" := by
  decide +kernel

/-- Names: `/\\` (HOL Light's printer) is the conjunction `/\`; any other escape is refused. -/
theorem control_unescape :
    unescape "/\\\\" = some "/\\" ∧ unescape "\\\\/" = some "\\/" ∧ unescape "a\\nb" = none := by
  decide +kernel

end Mettapedia.GSLT.Readers.HOL.Load
