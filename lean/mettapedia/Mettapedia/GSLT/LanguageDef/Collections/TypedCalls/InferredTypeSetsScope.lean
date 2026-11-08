import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.InferredTypeSets

/-!
# Inferred typing sets: the fixed literal rule and the escape rule's scope

Two rules of CeTTa's inference of typing sets
(`prepared_pure_infer_untyped`, `prepared_pure_static_types`), read against the
model of `InferredTypeSets`.

**A typing naming `%Undefined%` below its top is unknown**
(`prepared_pure_type_set_add`). HE reads `%Undefined%` as any type only at the
top of a type; inside one it is a type like any other. CeTTa's matcher reads it
as a wildcard at every depth, so CeTTa now makes a member naming it anywhere
unknown, and the machine declines a value whose typing names it. The fixed
literal rule (`litSetFix`) covers its literal (`covers_litFix`) and is at least
as wide as the model's (`litSet_le_litFix`); on the probe `(: x (List %Undefined%))`
it is unknown, so no check of `x` is discharged (`Controls.undefined_member_unknown`).
The other two fixes of round two are the model's own rules: a field read only
where the range fixes it (`InferredTypeSets.fieldSet`, with the refuting
program in `InferredTypeSets.Controls.free_field_not_lower`) and a failing
combination making the build unknown (`InferredTypeSets.buildSet`, with
`InferredTypeSets.Controls.failing_lower_combination_builds`).

**The escape rule is sufficient where no call is dynamic.** CeTTa makes a head's
inferred parameters unknown only where a bare symbol literal of the program names
it. In the model, the symbols named as values matter only to dynamic calls: a
program none of whose bodies calls through a value (`ProgNoDyn`) reaches the same
values whatever set of heads it names (`reach_withNamed`). So for such programs a
fixpoint with no escape condition at all (`postFix_noEscape`) makes the analysis
sound (`sound_noDyn`) and discharge exact (`prepared_iff_noDyn`). CeTTa's prepared
programs make no dynamic call: a head whose equations call through a variable is
classified impure and refused before a program is prepared, so CeTTa's narrower
escape rule is sufficient there. Where dynamic calls are admitted the condition is
needed (`InferredTypeSets.Controls.escape_needs_any`).

**Let slots read again.** CeTTa reads a `let` slot through its bound node,
analysed again at each use (`bound_by`). The conditions checked under one
covering assignment of slot sets make the analysis sound under any covering
assignment (`sound_any`), and a node's set reads only the slots the node reads
(`absNode_congr`), so the re-read set covers the slot's value wherever the slots
the node reads keep their values (`reread_covers`). A `let` of a slot already in
scope is an equality test in CeTTa's machine, which keeps that; a `let` of the
same variable in a sibling position is compiled as a new binding, where HE's
bindings persist through the evaluation of the rest of the body and make it a
test, so there the machine's run is not HE's (the semantics of the model is the
machine's, scoped `let`).

**A typed head at a formal with type variables** (`Controls.open_formal_program`):
`(: len (-> (List $a) Number))` called on `(Cons 1 Nil)`, its argument
discharged at `(List $a)`, the build discharged and the return shown, meets every
condition of a fixpoint of `InferredTypeSets`' model (now with such formals), so
the run skipping all three checks reaches exactly HE's values.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.InferredTypeSetsScope

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open ShapeTyping StaticEvidence InferredTypeSets

/-! ## The fixed literal rule -/

mutual
/-- Whether a type names the symbol `s` anywhere. -/
def mentions (s : String) : Ty String → Bool
  | .var _ => false
  | .sym t => t == s
  | .app ts => mentionsList s ts
/-- Whether some type of a list names the symbol `s`. -/
def mentionsList (s : String) : List (Ty String) → Bool
  | [] => false
  | t :: ts => mentions s t || mentionsList s ts
end

/-- A literal whose rows name `%Undefined%` anywhere. -/
def NamesUndefined (Γ : Decls) : Atom → Bool
  | .symbol s => (readRows (Γ s)).any (mentions "%Undefined%")
  | _ => false

/-- **CeTTa's literal rule with the fix**: unknown where the literal's row names
`%Undefined%` anywhere, the model's rule elsewhere. -/
def litSetFix (Γ : Decls) (a : Atom) : TySet := if NamesUndefined Γ a then none else litSet Γ a

/-- **The fixed literal rule covers its literal.** -/
theorem covers_litFix (Γ : Decls) (a : Atom) : Covers Γ (litSetFix Γ a) a := by
  unfold litSetFix
  split_ifs
  · trivial
  · exact covers_lit Γ a

/-- **The fix only widens**: every literal's fixed set is at least as wide as the
model's, so it discharges no check the model's set does not. -/
theorem litSet_le_litFix (Γ : Decls) (a : Atom) : Le (litSet Γ a) (litSetFix Γ a) := by
  unfold litSetFix
  split_ifs
  · exact le_none _
  · exact Le.refl _

/-! ## The escape rule where no call is dynamic -/

mutual
/-- A node calls no head through a value. -/
def NoDyn : Node → Prop
  | .slot _ => True
  | .lit _ => True
  | .reg _ args => NoDynAll args
  | .data _ args => NoDynAll args
  | .call _ args _ => NoDynAll args
  | .dyncall _ _ => False
  | .build _ args _ => NoDynAll args
  | .ite c t e => NoDyn c ∧ NoDyn t ∧ NoDyn e
  | .bind _ v b => NoDyn v ∧ NoDyn b
/-- No node of a list calls a head through a value. -/
def NoDynAll : List Node → Prop
  | [] => True
  | n :: ns => NoDyn n ∧ NoDynAll ns
end

theorem noDynAll_iff : ∀ ns : List Node, NoDynAll ns ↔ ∀ n ∈ ns, NoDyn n
  | [] => by simp [NoDynAll]
  | n :: ns => by simp [NoDynAll, noDynAll_iff ns]

/-- **A program without dynamic calls**: neither its run's body nor any equation
calls a head through a value. -/
def ProgNoDyn (P : Program) : Prop := NoDyn P.main ∧ ∀ h, ∀ e ∈ P.eqs h, NoDyn e.body

/-- The program naming the heads `N` as values. -/
def withNamed (P : Program) (N : Set String) : Program := { P with named := N }

theorem withNamed_withNamed (P : Program) (N : Set String) : withNamed (withNamed P N) P.named = P := by
  cases P
  rfl

/-- **Without dynamic calls the named heads do not matter**: every value a node
without dynamic calls reaches, it reaches in the program naming any other heads. -/
theorem reach_withNamed {Γ : Decls} {P : Program} {prep : Bool} (N : Set String)
    (bodies : ∀ h, ∀ e ∈ P.eqs h, NoDyn e.body) {env : ℕ → Atom} {n : Node} {v : Atom}
    (hr : Reach Γ P prep env n v) : NoDyn n → Reach Γ (withNamed P N) prep env n v := by
  induction hr with
  | slot env s => intro _; exact .slot env s
  | lit env a => intro _; exact .lit env a
  | reg env cls args ws g len each hg each_ih =>
      intro hn
      exact .reg env cls args ws g len (fun p hp => each_ih p hp
        ((noDynAll_iff args).mp hn p.1 (List.of_mem_zip hp).1)) hg
  | data env c args ws len each each_ih =>
      intro hn
      exact .data env c args ws len (fun p hp => each_ih p hp
        ((noDynAll_iff args).mp hn p.1 (List.of_mem_zip hp).1))
  | call env h args skip ws e env' r len each he hm hc hr hrange each_ih hr_ih =>
      intro hn
      exact .call env h args skip ws e env' r len (fun p hp => each_ih p hp
        ((noDynAll_iff args).mp hn p.1 (List.of_mem_zip hp).1)) he hm hc (hr_ih (bodies h e he)) hrange
  | dyncall => intro hn; exact hn.elim
  | build env c args skip ws len each hc each_ih =>
      intro hn
      exact .build env c args skip ws len (fun p hp => each_ih p hp
        ((noDynAll_iff args).mp hn p.1 (List.of_mem_zip hp).1)) hc
  | iteT env c t e w r hc ht hc_ih ht_ih =>
      intro hn
      exact .iteT env c t e w r (hc_ih hn.1) (ht_ih hn.2.1)
  | iteE env c t e w r hc he hc_ih he_ih =>
      intro hn
      exact .iteE env c t e w r (hc_ih hn.1) (he_ih hn.2.2)
  | bind env s v b w r hv hb hv_ih hb_ih =>
      intro hn
      exact .bind env s v b w r (hv_ih hn.1) (hb_ih hn.2)

section Renamed

variable (Γ : Decls) (P : Program) (N : Set String) (St : Stored)

mutual
/-- The analysis reads no named head. -/
theorem absNode_withNamed : ∀ (aenv : ℕ → TySet) (n : Node),
    absNode Γ (withNamed P N) St aenv n = absNode Γ P St aenv n
  | _, .slot _ => rfl
  | _, .lit _ => rfl
  | _, .reg _ _ => rfl
  | _, .data _ _ => rfl
  | _, .call _ _ _ => rfl
  | _, .dyncall _ _ => rfl
  | aenv, .build c args _ => by
      simp only [absNode]
      rw [absNodes_withNamed aenv args]
  | aenv, .ite _ t e => by
      simp only [absNode]
      rw [absNode_withNamed aenv t, absNode_withNamed aenv e]
  | aenv, .bind x v b => by
      simp only [absNode]
      rw [absNode_withNamed aenv v, absNode_withNamed _ b]
theorem absNodes_withNamed : ∀ (aenv : ℕ → TySet) (ns : List Node),
    absNodes Γ (withNamed P N) St aenv ns = absNodes Γ P St aenv ns
  | _, [] => rfl
  | aenv, n :: ns => by
      simp only [absNodes]
      rw [absNode_withNamed aenv n, absNodes_withNamed aenv ns]
end

mutual
/-- A body's conditions read no named head. -/
theorem walk_withNamed : ∀ (aenv : ℕ → TySet) (n : Node),
    InferredTypeSets.Walk Γ (withNamed P N) St aenv n ↔ InferredTypeSets.Walk Γ P St aenv n
  | _, .slot _ => Iff.rfl
  | _, .lit _ => Iff.rfl
  | aenv, .reg _ args => by
      simp only [InferredTypeSets.Walk]
      exact walkAll_withNamed aenv args
  | aenv, .data _ args => by
      simp only [InferredTypeSets.Walk]
      exact walkAll_withNamed aenv args
  | aenv, .call h args skip => by
      simp only [InferredTypeSets.Walk]
      rw [absNodes_withNamed]
      exact and_congr (walkAll_withNamed aenv args) Iff.rfl
  | aenv, .dyncall f args => by
      simp only [InferredTypeSets.Walk]
      exact and_congr (walk_withNamed aenv f) (walkAll_withNamed aenv args)
  | aenv, .build c args skip => by
      simp only [InferredTypeSets.Walk]
      rw [absNodes_withNamed]
      exact and_congr (walkAll_withNamed aenv args) Iff.rfl
  | aenv, .ite c t e => by
      simp only [InferredTypeSets.Walk]
      exact and_congr (walk_withNamed aenv c) (and_congr (walk_withNamed aenv t) (walk_withNamed aenv e))
  | aenv, .bind x v b => by
      simp only [InferredTypeSets.Walk]
      rw [absNode_withNamed]
      exact and_congr (walk_withNamed aenv v) (walk_withNamed _ b)
theorem walkAll_withNamed : ∀ (aenv : ℕ → TySet) (ns : List Node),
    InferredTypeSets.WalkAll Γ (withNamed P N) St aenv ns ↔ InferredTypeSets.WalkAll Γ P St aenv ns
  | _, [] => Iff.rfl
  | aenv, n :: ns => by
      simp only [InferredTypeSets.WalkAll]
      exact and_congr (walk_withNamed aenv n) (walkAll_withNamed aenv ns)
end

end Renamed

/-- **A fixpoint without the escape condition**: the conditions of a fixpoint
other than the one on heads named as values make a fixpoint of the program naming
no head. -/
theorem postFix_noEscape {Γ : Decls} {P : Program} {St : Stored}
    (main : InferredTypeSets.Walk Γ P St (fun _ => none) P.main)
    (eqs : ∀ h, ∀ e ∈ P.eqs h, InferredTypeSets.Walk Γ P St (entryEnv Γ P St h e) e.body)
    (answers : ∀ h, P.formals h = none → ∀ e ∈ P.eqs h,
      Le (absNode Γ P St (entryEnv Γ P St h e) e.body) (St.answer h))
    (shown : ∀ h R, P.range h = some R → P.shown h = true → ∀ e ∈ P.eqs h,
      ∃ Ms, absNode Γ P St (entryEnv Γ P St h e) e.body = some Ms ∧ ∀ S ∈ Ms, R ∈ S) :
    PostFix Γ (withNamed P ∅) St where
  main := (walk_withNamed Γ P ∅ St _ _).mpr main
  eqs h e he := (walk_withNamed Γ P ∅ St _ _).mpr (eqs h e he)
  answers h hf e he := by
    rw [absNode_withNamed]
    exact answers h hf e he
  escaped _ h := h.elim
  shown h R hR hs e he := by
    rw [absNode_withNamed]
    exact shown h R hR hs e he

/-- **Soundness without dynamic calls**: under a fixpoint with no escape
condition, every value a node without dynamic calls reaches in HE's run is
covered by the node's set. -/
theorem sound_noDyn {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ (withNamed P ∅) St)
    (wf : WF Γ P) (bodies : ∀ h, ∀ e ∈ P.eqs h, NoDyn e.body) {env : ℕ → Atom} {n : Node} {v : Atom}
    (hr : Reach Γ P false env n v) (hn : NoDyn n) :
    ∀ aenv, EnvCovers Γ aenv env → InferredTypeSets.Walk Γ P St aenv n →
      Covers Γ (absNode Γ P St aenv n) v := by
  intro aenv hcov hwalk
  rw [← absNode_withNamed Γ P ∅ St]
  exact sound fix ⟨wf.formals, wf.range⟩ (reach_withNamed ∅ bodies hr hn) aenv hcov
    ((walk_withNamed Γ P ∅ St aenv n).mpr hwalk)

/-- **Discharge is exact without dynamic calls**: under a fixpoint with no escape
condition, the run that skips the discharged checks reaches exactly HE's values,
whatever heads the program names as values. -/
theorem prepared_iff_noDyn {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ (withNamed P ∅) St)
    (wf : WF Γ P) (noDyn : ProgNoDyn P) (env : ℕ → Atom) (v : Atom) :
    Reach Γ P true env P.main v ↔ Reach Γ P false env P.main v := by
  have back : ∀ prep, Reach Γ (withNamed P ∅) prep env P.main v → Reach Γ P prep env P.main v := by
    intro prep h
    have := reach_withNamed (P := withNamed P ∅) P.named noDyn.2 h noDyn.1
    rwa [withNamed_withNamed] at this
  constructor
  · intro h
    exact back false ((prepared_iff fix ⟨wf.formals, wf.range⟩ env v).mp
      (reach_withNamed ∅ noDyn.2 h noDyn.1))
  · intro h
    exact back true ((prepared_iff fix ⟨wf.formals, wf.range⟩ env v).mpr
      (reach_withNamed ∅ noDyn.2 h noDyn.1))

/-! ## Let slots read again through their bound node

CeTTa's analysis reads a `let` slot through the node it is bound to, analysed
again at each use with the sets the analysis has there (`bound_by`), where the
model reads the bound value's set at the `let`. A `let` of a slot already bound
is an equality test in CeTTa's machine (the slot keeps its value), so a slot's
value never changes in its scope, and the sets at a later point still cover the
slots there. Two facts make the re-reading sound: the conditions checked under
one covering assignment of slot sets make the analysis sound under any covering
assignment (`sound_any`), and a node's set reads only the slots the node reads
(`absNode_congr`). Together (`reread_covers`): the bound node's set under the
later sets covers the slot's value wherever the slots the node reads still hold
their values. -/

/-- **The analysis is sound under any covering slot sets**: with the conditions
of a node checked under slot sets covering the slots, every value the node
reaches in HE's run is covered by its set under any other slot sets covering the
slots. -/
theorem sound_any {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ P St) (wf : WF Γ P)
    {env : ℕ → Atom} {n : Node} {v : Atom} (hr : Reach Γ P false env n v) :
    ∀ aenv aenv' : ℕ → TySet, EnvCovers Γ aenv env → InferredTypeSets.Walk Γ P St aenv n →
      EnvCovers Γ aenv' env → Covers Γ (absNode Γ P St aenv' n) v := by
  induction hr with
  | slot env s => intro _ _ _ _ hcov'; exact hcov' s
  | lit env a => intro _ _ _ _ _; exact covers_lit Γ a
  | reg env cls args ws g len each hg =>
      intro aenv _ hcov hwalk _
      exact sound fix wf (.reg env cls args ws g len each hg) aenv hcov hwalk
  | data => intro _ _ _ _ _; trivial
  | call env h args skip ws e env' r len each he hm hc hr hrange =>
      intro aenv _ hcov hwalk _
      exact sound fix wf (.call env h args skip ws e env' r len each he hm hc hr hrange) aenv hcov hwalk
  | dyncall => intro _ _ _ _ _; trivial
  | build env c args skip ws len each hc each_ih =>
      intro aenv aenv' hcov hwalk hcov'
      simp only [InferredTypeSets.Walk] at hwalk
      simp only [absNode]
      apply covers_build
      rw [absNodes_eq_map]
      refine List.forall₂_map_left_iff.mpr (forall₂_of_zip len fun p hp => ?_)
      exact each_ih p hp aenv aenv' hcov
        ((walkAll_iff Γ P St aenv args).mp hwalk.1 p.1 (List.of_mem_zip hp).1) hcov'
  | iteT env c t e w r hc ht hc_ih ht_ih =>
      intro aenv aenv' hcov hwalk hcov'
      simp only [InferredTypeSets.Walk] at hwalk
      simp only [absNode]
      exact covers_join_left _ (ht_ih aenv aenv' hcov hwalk.2.1 hcov')
  | iteE env c t e w r hc he hc_ih he_ih =>
      intro aenv aenv' hcov hwalk hcov'
      simp only [InferredTypeSets.Walk] at hwalk
      simp only [absNode]
      exact covers_join_right _ (he_ih aenv aenv' hcov hwalk.2.2 hcov')
  | bind env s v b w r hv hb hv_ih hb_ih =>
      intro aenv aenv' hcov hwalk hcov'
      simp only [InferredTypeSets.Walk] at hwalk
      simp only [absNode]
      exact hb_ih _ _ (envCovers_update hcov s (sound fix wf hv aenv hcov hwalk.1)) hwalk.2
        (envCovers_update hcov' s (hv_ih aenv aenv' hcov hwalk.1 hcov'))

mutual
/-- The slots a node reads: a `let` reads its value's and its body's other
than its own. -/
def Reads : Node → ℕ → Prop
  | .slot s, t => t = s
  | .lit _, _ => False
  | .reg _ args, t => ReadsAll args t
  | .data _ args, t => ReadsAll args t
  | .call _ args _, t => ReadsAll args t
  | .dyncall f args, t => Reads f t ∨ ReadsAll args t
  | .build _ args _, t => ReadsAll args t
  | .ite c th el, t => Reads c t ∨ Reads th t ∨ Reads el t
  | .bind s v b, t => Reads v t ∨ (Reads b t ∧ t ≠ s)
/-- The slots a list of nodes reads. -/
def ReadsAll : List Node → ℕ → Prop
  | [], _ => False
  | n :: ns, t => Reads n t ∨ ReadsAll ns t
end

mutual
/-- **A node's set reads only the slots the node reads.** -/
theorem absNode_congr (Γ : Decls) (P : Program) (St : Stored) :
    ∀ (n : Node) {aenv aenv' : ℕ → TySet}, (∀ t, Reads n t → aenv t = aenv' t) →
      absNode Γ P St aenv n = absNode Γ P St aenv' n
  | .slot s, _, _, h => h s rfl
  | .lit _, _, _, _ => rfl
  | .reg _ _, _, _, _ => rfl
  | .data _ _, _, _, _ => rfl
  | .call _ _ _, _, _, _ => rfl
  | .dyncall _ _, _, _, _ => rfl
  | .build c args _, _, _, h => by
      simp only [absNode]
      rw [absNodes_congr Γ P St args h]
  | .ite c th el, _, _, h => by
      simp only [absNode]
      rw [absNode_congr Γ P St th fun t ht => h t (.inr (.inl ht)),
        absNode_congr Γ P St el fun t ht => h t (.inr (.inr ht))]
  | .bind x v b, aenv, aenv', h => by
      simp only [absNode]
      have hv := absNode_congr Γ P St v (aenv := aenv) (aenv' := aenv') fun t ht => h t (.inl ht)
      refine absNode_congr Γ P St b fun t ht => ?_
      by_cases htx : t = x
      · subst htx
        simp [hv]
      · simp only [Function.update, htx, dif_neg, not_false_eq_true]
        exact h t (.inr ⟨ht, htx⟩)
theorem absNodes_congr (Γ : Decls) (P : Program) (St : Stored) :
    ∀ (ns : List Node) {aenv aenv' : ℕ → TySet}, (∀ t, ReadsAll ns t → aenv t = aenv' t) →
      absNodes Γ P St aenv ns = absNodes Γ P St aenv' ns
  | [], _, _, _ => rfl
  | n :: ns, _, _, h => by
      simp only [absNodes]
      rw [absNode_congr Γ P St n fun t ht => h t (.inl ht),
        absNodes_congr Γ P St ns fun t ht => h t (.inr ht)]
end

/-- **CeTTa's re-reading of a let slot is covered**: a `let` bound `n` to the
value `w` under slot sets covering its slots, with `n`'s conditions checked there;
at a later point where the slots `n` reads hold the same values, `n`'s set under
any slot sets covering the slots there covers `w`. -/
theorem reread_covers {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ P St) (wf : WF Γ P)
    {envLet envUse : ℕ → Atom} {n : Node} {w : Atom} (hn : Reach Γ P false envLet n w)
    (same : ∀ t, Reads n t → envLet t = envUse t) {aenvLet aenvUse : ℕ → TySet}
    (hcovLet : EnvCovers Γ aenvLet envLet) (hwalk : InferredTypeSets.Walk Γ P St aenvLet n)
    (hcovUse : EnvCovers Γ aenvUse envUse) : Covers Γ (absNode Γ P St aenvUse n) w := by
  classical
  let mixed : ℕ → TySet := fun t => if Reads n t then aenvUse t else aenvLet t
  have hcovMixed : EnvCovers Γ mixed envLet := by
    intro t
    by_cases ht : Reads n t
    · simp only [mixed, if_pos ht]
      rw [same t ht]
      exact hcovUse t
    · simp only [mixed, if_neg ht]
      exact hcovLet t
  have key := sound_any fix wf hn aenvLet mixed hcovLet hwalk hcovMixed
  rwa [absNode_congr Γ P St n (aenv := mixed) (aenv' := aenvUse) fun t ht => by simp [mixed, ht]] at key

/-! ## Controls -/

namespace Controls

open ShapeTyping.Controls (tc listT decls)
open InferredTypeSets.Controls (xdecls)

/-- **The fixed rule makes `x : (List %Undefined%)` unknown** (probes
`nested_undefined_literal*`): no member, so no check of `x` is discharged, while
the model's rule gives the member `(List %Undefined%)`. -/
theorem undefined_member_unknown :
    litSetFix xdecls (.symbol "x") = none ∧ litSet xdecls (.symbol "x") ≠ none := by
  have hr : readRows (xdecls "x") = [listT (tc "%Undefined%")] := by
    simp [xdecls, readRows, listT, tc, undefinedTy]
  refine ⟨?_, ?_⟩
  · simp [litSetFix, NamesUndefined, hr, listT, tc, mentions, mentionsList]
  · simp [litSet, hr]

/-- The escape program of round two calls `u` dynamically. -/
theorem escProg_dyn : ¬ NoDyn InferredTypeSets.Controls.escProg.main := by
  simp [InferredTypeSets.Controls.escProg, InferredTypeSets.Controls.escMain, NoDyn]

/-! ### A typed head at a formal with type variables -/

open ShapeTyping.Controls (tv gc glist num consRow)
open InferredTypeSets.Controls (ctorRow_cons joint_cons)

/-- `(: len (-> (List $a) Number))`, `(= (len $l) 7)`, called as
`(len (Cons 1 Nil))` with the argument's check and the build's check discharged. -/
def lenProg : Program where
  eqs := fun h => if h = "len" then [⟨1, fun _ => .whole 0, .lit (num 7)⟩] else []
  formals := fun h => if h = "len" then some [some (listT (tv "a"))] else none
  range := fun h => if h = "len" then some (gc "Number") else none
  shown := fun h => h = "len"
  named := ∅
  main := .call "len" [.build "Cons" [.lit (num 1), .lit (.symbol "Nil")] true] [true]

/-- The build's typing: `(List Number)`. -/
def consSet : Set (Ty Empty) :=
  combo [tv "x", listT (tv "x")] (listT (tv "x")) [{gc "Number"}, inst (listT (tv "x"))]

theorem list_number_in_consSet : glist (gc "Number") ∈ consSet :=
  ⟨fun _ => gc "Number", (joint_cons _ _ _).mpr ⟨rfl, fun _ => gc "Number", rfl⟩, rfl⟩

/-- `len`'s inferred parameter: the build's set. -/
def lenSt : Stored where
  param := fun _ _ => some [consSet]
  answer := fun _ => none

theorem nil_lit : litSet decls (.symbol "Nil") = some [inst (listT (tv "x"))] := by
  simp [litSet, ShapeTyping.Controls.decls, readRows, listT, tv, undefinedTy]

theorem lenProg_lits : absNodes decls lenProg lenSt (fun _ => none) [.lit (num 1), .lit (.symbol "Nil")] =
    [some [{gc "Number"}], some [inst (listT (tv "x"))]] := by
  simp only [absNodes, absNode, nil_lit]
  rfl

theorem cons_passes : BuildPasses decls "Cons" [some [{gc "Number"}], some [inst (listT (tv "x"))]] := by
  refine ⟨consRow, _, _, ctorRow_cons, rfl, .inr ⟨[[{gc "Number"}], [inst (listT (tv "x"))]], rfl, ?_⟩⟩
  intro Ss hSs
  simp only [List.sections, List.flatMap_cons, List.map_cons, List.map_nil, List.flatMap_nil,
    List.append_nil, List.mem_singleton] at hSs
  subst hSs
  exact ⟨_, list_number_in_consSet⟩

theorem lenProg_build : absNode decls lenProg lenSt (fun _ => none)
    (.build "Cons" [.lit (num 1), .lit (.symbol "Nil")] true) = some [consSet] := by
  show buildSet decls "Cons" (absNodes decls lenProg lenSt (fun _ => none) [.lit (num 1), .lit (.symbol "Nil")]) = _
  rw [lenProg_lits]
  unfold buildSet
  rw [ctorRow_cons]
  simp only [List.length_cons, List.length_nil, if_true, scan, Scan.cons]
  rw [if_pos]
  · rfl
  · intro Ss hSs
    simp only [List.sections, List.flatMap_cons, List.map_cons, List.map_nil, List.flatMap_nil,
      List.append_nil, List.mem_singleton] at hSs
    subst hSs
    exact ⟨_, list_number_in_consSet⟩

/-- **A typed head at a formal with type variables in a program**: the
argument `(Cons 1 Nil)` is discharged at `(List $a)` (its member `(List Number)`
allows an instance), the call site joins its set into `len`'s inferred
parameter, the build is discharged, and `len`'s return is shown; every condition
of a fixpoint holds, so skipping all three checks reaches exactly HE's values. -/
theorem open_formal_program :
    PostFix decls lenProg lenSt ∧ WF decls lenProg ∧
      ∀ env v, Reach decls lenProg true env lenProg.main v ↔ Reach decls lenProg false env lenProg.main v := by
  have hF : lenProg.formals "len" = some [some (listT (tv "a"))] := rfl
  have hkids : absNodes decls lenProg lenSt (fun _ => none)
      [.build "Cons" [.lit (num 1), .lit (.symbol "Nil")] true] = [some [consSet]] := by
    simp only [absNodes, lenProg_build]
  have post : PostFix decls lenProg lenSt := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show InferredTypeSets.Walk decls lenProg lenSt (fun _ => none)
        (.call "len" [.build "Cons" [.lit (num 1), .lit (.symbol "Nil")] true] [true])
      simp only [InferredTypeSets.Walk, InferredTypeSets.WalkAll, CallOK, hF, hkids, lenProg_lits]
      refine ⟨⟨⟨⟨trivial, trivial, trivial⟩, fun _ => cons_passes⟩, trivial⟩, ?_, ?_⟩
      · intro j hj
        cases j with
        | zero =>
            refine ⟨listT (tv "a"), rfl, [consSet], rfl, fun S hS => ?_⟩
            simp only [List.mem_singleton] at hS
            subst hS
            exact ⟨fun _ => gc "Number", list_number_in_consSet⟩
        | succ j => simp at hj
      · intro j F k hFj _ hk
        cases j with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
            subst hk
            exact Le.refl _
        | succ j => simp at hFj
    · intro h e he
      by_cases hl : h = "len"
      · subst hl
        have : e = ⟨1, fun _ => .whole 0, .lit (num 7)⟩ := by simpa [lenProg] using he
        subst this
        trivial
      · simp [lenProg, hl] at he
    · intro h hFh e he
      by_cases hl : h = "len"
      · subst hl
        simp [lenProg] at hFh
      · simp [lenProg, hl] at he
    · intro h hh
      exact absurd hh (Set.notMem_empty h)
    · intro h R hR _ e he
      by_cases hl : h = "len"
      · subst hl
        have hR' : R = gc "Number" := by simpa [lenProg] using hR.symm
        have he' : e = ⟨1, fun _ => .whole 0, .lit (num 7)⟩ := by simpa [lenProg] using he
        subst hR'
        subst he'
        exact ⟨[{gc "Number"}], rfl, fun S hS => by
          simp only [List.mem_singleton] at hS
          subst hS
          rfl⟩
      · simp [lenProg, hl] at hR
  have wf : WF decls lenProg := by
    refine ⟨fun h Fs hFs F hFm => ?_, fun h R hR => ?_⟩
    · by_cases hl : h = "len"
      · subst hl
        rw [hF] at hFs
        simp only [Option.some.injEq] at hFs
        subst hFs
        simp only [List.mem_singleton, Option.some.injEq] at hFm
        subst hFm
        intro v
        rfl
      · simp [lenProg, hl] at hFs
    · by_cases hl : h = "len"
      · subst hl
        have hR' : R = gc "Number" := by simpa [lenProg] using hR.symm
        subst hR'
        intro v
        cases v <;> rfl
      · simp [lenProg, hl] at hR
  exact ⟨post, wf, fun env v => prepared_iff post wf env v⟩

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.InferredTypeSetsScope
