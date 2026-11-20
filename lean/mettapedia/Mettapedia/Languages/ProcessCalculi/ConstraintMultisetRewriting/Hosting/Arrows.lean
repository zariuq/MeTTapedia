import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Hosting

/-!
# `let` on the step: the two control rules, and the hygiene the correspondence needs

`let_ s p c k` runs `c`, then binds each answer to the pattern `p` and runs `k`. The source opens the
names of the site `s` at a fresh scope when it binds (`Move.letBind`, `openAt`). The translation
opens them earlier: an equation's firing opens every name of its right-hand side, the `let`'s names
included; the fixed rules `bindStartRule` (push the frame) and `bindValueRule` (tell `P ≐ T`, run the
body) do not open anything.

* `transfer_bindStart`: pushing the frame transforms readings exactly as the source's `letStart`.
* `transfer_bindValue`: telling the pattern equal to the value transforms readings exactly as the
  source's `letBind`, **for a hygienic frame** (`FramePrivate`): the store, the value and the rest of
  the stack do not depend on the names the frame binds. One direction needs only freshness
  (`bindValue_forward`); the other needs hygiene.
* `hygiene_needed`: the control. An alternative whose store already binds the frame's own name `x`
  to `two`, receiving `one`: the source's bind (a fresh copy of `x`) has a reading, `one`; the
  readings of the rule's made row are empty. So hygiene cannot be dropped; it is a sufficient
  condition, not a characterization (an alternative may mention an own name without breaking the bind).
* `simulation_letStart`, `simulation_letBind`, `reflection_bindStart`, `reflection_bindValue`: the
  step correspondence for the two `let` moves, one firing each, the second for hygienic frames.

That every alternative reachable from a well-formed query and program is hygienic is proved in
`Hygiene` (`reachableHygienic_of_wellFormed`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S} {Ty : Type}

/-! ## Opening at a scope, read back -/

section Open

variable {W : Type} {target : W → MetaArity S}

/-- The scopes of a name after opening the site `s` at `n`. -/
def openScopes (s : κ.Site) (n : ℕ) (x : Name κ) : List ℕ :=
  if κ.site x.key = s then n :: x.scopes else x.scopes

/-- The scopes of a name with an opening of the site `s` at `n` undone. -/
def unopenScopes (s : κ.Site) (n : ℕ) (x : Name κ) : List ℕ :=
  match x.scopes with
  | m :: rest => if m = n ∧ κ.site x.key = s then rest else m :: rest
  | [] => []

theorem unopen_open (s : κ.Site) (n : ℕ) (y : Name κ) :
    unopenScopes s n ⟨openScopes s n y, y.key⟩ = y.scopes := by
  by_cases site : κ.site y.key = s
  · simp [openScopes, unopenScopes, site]
  · rcases y with ⟨scopes, key⟩
    cases scopes <;> simp_all [openScopes, unopenScopes]

theorem unopen_below {s : κ.Site} {n : ℕ} {x : Name κ} (below : Below n x) :
    unopenScopes s n x = x.scopes := by
  rcases x with ⟨scopes, key⟩
  cases scopes with
  | nil => rfl
  | cons m rest =>
      have small : m < n := below m rfl
      simp [unopenScopes, Nat.ne_of_lt small]

/-- Read every name of site `s` opened at scope `n` as `σ` reads the unopened name. -/
def graftOpen (s : κ.Site) (n : ℕ) (σ : Assignment (fam κ) target) : Assignment (fam κ) target :=
  fun x => σ ⟨unopenScopes s n x, x.key⟩

theorem read_scopes (σ : Assignment (fam κ) target) {key : κ.Key} {l l' : List ℕ} (same : l = l') :
    (σ ⟨l, key⟩ : Term (signature S target) (κ.arity key).1 (κ.arity key).2) = σ ⟨l', key⟩ := by
  subst same; rfl

theorem graftOpen_below {s : κ.Site} {n : ℕ} (σ : Assignment (fam κ) target) {x : Name κ}
    (below : Below n x) : graftOpen s n σ x = σ x :=
  read_scopes σ (unopen_below below)

theorem openAt_eq (s : κ.Site) (n : ℕ) (y : Name κ) :
    openAt κ s n y = generator (fam κ) ⟨openScopes s n y, y.key⟩ := rfl

theorem graftOpen_open (s : κ.Site) (n : ℕ) (σ : Assignment (fam κ) target) {Δ : Ctx S} {sort : S.Srt}
    (t : Term (signature S (fam κ)) Δ sort) :
    instantiate (graftOpen s n σ) (instantiate (openAt κ s n) t) = instantiate σ t := by
  rw [instantiate_comp]
  apply congrArg (fun ρ => instantiate ρ t)
  funext y
  rw [openAt_eq, instantiate_generator]
  exact read_scopes σ (unopen_open s n y)

theorem dependsBelow_open {n : ℕ} (s : κ.Site) {Δ : Ctx S} {sort : S.Srt}
    {t : Term (signature S (fam κ)) Δ sort} (depends : DependsBelow n t) :
    DependsBelow (n + 1) (instantiate (openAt κ s n) t) := by
  intro W' target' σ σ' agree
  rw [instantiate_comp, instantiate_comp]
  apply depends
  intro y below
  rw [openAt_eq, instantiate_generator, instantiate_generator]
  apply agree
  intro m head
  by_cases site : κ.site y.key = s
  · simp only [openScopes, site, if_true, List.head?_cons, Option.some.injEq] at head
    omega
  · simp only [openScopes, site, if_false] at head
    exact Nat.lt_of_lt_of_le (below m head) (Nat.le_succ n)

end Open

/-! ## Hygiene -/

/-- The names a pending `let` frame binds: those of its site in its pattern or its body. -/
def OwnName (s : κ.Site) (p : Data κ Γ star) (k : Comp κ Γ star Ty) (x : Name κ) : Prop :=
  κ.site x.key = s ∧ (x ∈ support p ∨ ∃ t ∈ k.data, x ∈ support t)

/-- **A hygienic frame**: the store, the value and the rest of the stack do not depend on the names
the frame binds. -/
def FramePrivate (s : κ.Site) (p : Data κ Γ star) (k : Comp κ Γ star Ty) (K : List (Constraint κ Γ star))
    (v : Data κ Γ star) (fs : List (SourceLanguage.Frame κ Γ star Ty)) : Prop :=
  ∀ {W : Type} {target : W → MetaArity S} (σ σ' : Assignment (fam κ) target),
    (∀ x, ¬ OwnName s p k x → σ x = σ' x) →
      (∀ e ∈ K, instantiate σ e.1 = instantiate σ' e.1 ∧ instantiate σ e.2 = instantiate σ' e.2) ∧
      instantiate σ v = instantiate σ' v ∧
      ∀ fr ∈ fs, ∀ t ∈ frameData fr, instantiate σ t = instantiate σ' t

/-! ## The transfers -/

section Transfers

variable {B : Interface.Frames.Frame S}

/-- **Pushing the frame.** -/
theorem transfer_bindStart {b : Branch κ Γ star Ty} {s : κ.Site} {p : Data κ Γ star}
    {c k : Comp κ Γ star Ty} (focus : b.focus = .eval (.let_ s p c k)) (q : Observation S B.arity) :
    (∃ h : Assignment (unknownArity Γ star) B.arity,
      branchReads N b B (instantiateObservation h
        (observe (altN N (evalN N (bindN N (unk .pattern) (unk .first) (unk .second))) (unk .stack)))) ∧
      (Interface.Frames.contextual S).Models (a := controlFrame Γ star) (b := B) h [] ∧
      instantiateObservation h (observe (altN N (evalN N (unk .first))
        (pushN N (unk .pattern) (unk .second) (unk .stack)))) = q) ↔
      branchReads N ⟨b.store, .eval c, .bindTo s p k :: b.frames, b.pending⟩ B q := by
  constructor
  · rintro ⟨h, reads, _, rfl⟩
    change branchReads N b B (observe (instantiate h _)) at reads
    rw [instantiate_altN, instantiate_evalN, instantiate_bindN, instantiate_unk, instantiate_unk,
      instantiate_unk, instantiate_unk] at reads
    obtain ⟨σ, solved, same⟩ := (branchReads_observe N).mp reads
    rw [encBranch, encAlt, focus] at same
    obtain ⟨onFocus, onStack⟩ := vec2_inj (N.args_eq same)
    obtain ⟨onPattern, onFirst, onSecond⟩ := vec3_inj (N.args_eq (vec1_inj (N.args_eq onFocus)))
    refine ⟨σ, solved, ?_⟩
    change observe _ = observe (instantiate h _)
    rw [instantiate_altN, instantiate_evalN, instantiate_pushN, instantiate_unk, instantiate_unk,
      instantiate_unk, instantiate_unk]
    simp only [encBranch, encAlt, encFocus, encStack]
    rw [onPattern, onFirst, onSecond, onStack]
  · rintro ⟨σ, solved, rfl⟩
    refine ⟨fill (instantiate σ p) (instantiate σ p) (encComp N (instantiate σ) c)
      (encComp N (instantiate σ) k) (encStack N (instantiate σ) b.frames), ?_, models_nil_tells _, ?_⟩
    · refine ⟨σ, solved, ?_⟩
      change observe _ = observe (instantiate _ _)
      rw [instantiate_altN, instantiate_evalN, instantiate_bindN, instantiate_unk, instantiate_unk,
        instantiate_unk, instantiate_unk]
      simp only [encBranch, encAlt, focus, encFocus, encComp, fill]
    · change observe (instantiate _ _) = _
      rw [instantiate_altN, instantiate_evalN, instantiate_pushN, instantiate_unk, instantiate_unk,
        instantiate_unk, instantiate_unk]
      rfl

/-- The take pattern of `bindValueRule`. -/
abbrev bindValuePattern : Observation S (unknownArity Γ star) :=
  observe (altN N (valueN N (unk .datum)) (pushN N (unk .pattern) (unk .second) (unk .stack)))

/-- The made row of `bindValueRule`. -/
abbrev bindValueMade : Observation S (unknownArity Γ star) :=
  observe (altN N (evalN N (unk .second)) (unk .stack))

/-- The tell of `bindValueRule`. -/
abbrev bindValueTell : EquationStore (Observation S (unknownArity Γ star)) :=
  [(observe (unk .pattern), observe (unk .datum))]

/-- What the rule's side of a bind reads: the body and the rest of the stack under the solutions of
the store that make the pattern equal to the value. -/
theorem bindValue_rule_side {K : List (Constraint κ Γ star)} {v : Data κ Γ star} {s : κ.Site}
    {p : Data κ Γ star} {k : Comp κ Γ star Ty} {fs : List (SourceLanguage.Frame κ Γ star Ty)}
    {ps : List (Data κ Γ star × Comp κ Γ star Ty)} (q : Observation S B.arity) :
    (∃ h : Assignment (unknownArity Γ star) B.arity,
      branchReads N ⟨K, .value v, .bindTo s p k :: fs, ps⟩ B (instantiateObservation h (bindValuePattern N)) ∧
      (Interface.Frames.contextual S).Models (a := controlFrame Γ star) (b := B) h
        (bindValueTell (Γ := Γ) (star := star)) ∧
      instantiateObservation h (bindValueMade N) = q) ↔
      ∃ σ : Assignment (fam κ) B.arity, Models σ K ∧ instantiate σ p = instantiate σ v ∧
        q = observe (altN N (evalN N (encComp N (instantiate σ) k)) (encStack N (instantiate σ) fs)) := by
  constructor
  · rintro ⟨h, reads, told, rfl⟩
    change branchReads N _ B (observe (instantiate h _)) at reads
    rw [instantiate_altN, instantiate_valueN, instantiate_pushN, instantiate_unk, instantiate_unk,
      instantiate_unk, instantiate_unk] at reads
    obtain ⟨σ, solved, same⟩ := (branchReads_observe N).mp reads
    simp only [encBranch, encAlt, encFocus, encStack] at same
    obtain ⟨onFocus, onStack⟩ := vec2_inj (N.args_eq same)
    have onValue := vec1_inj (N.args_eq onFocus)
    obtain ⟨onPattern, onSecond, onRest⟩ := vec3_inj (N.args_eq onStack)
    have tell := told _ (List.mem_singleton_self _)
    change observe (instantiate h (unk .pattern)) = observe (instantiate h (unk .datum)) at tell
    rw [instantiate_unk, instantiate_unk] at tell
    have tell' := observe_injective tell
    refine ⟨σ, solved, ?_, ?_⟩
    · rw [onPattern, onValue, tell']
    · change observe (instantiate h _) = _
      rw [instantiate_altN, instantiate_evalN, instantiate_unk, instantiate_unk, onSecond, onRest]
  · rintro ⟨σ, solved, matched, rfl⟩
    refine ⟨fill (instantiate σ v) (instantiate σ p) (encComp N (instantiate σ) k)
      (encComp N (instantiate σ) k) (encStack N (instantiate σ) fs), ⟨σ, solved, ?_⟩, ?_, ?_⟩
    · change observe _ = observe (instantiate _ _)
      rw [instantiate_altN, instantiate_valueN, instantiate_pushN, instantiate_unk, instantiate_unk,
        instantiate_unk, instantiate_unk]
      rfl
    · intro e member
      rw [List.mem_singleton.mp member]
      change observe (instantiate _ (unk .pattern)) = observe (instantiate _ (unk .datum))
      rw [instantiate_unk, instantiate_unk]
      exact congrArg observe matched
    · change observe (instantiate _ _) = _
      rw [instantiate_altN, instantiate_evalN, instantiate_unk, instantiate_unk]
      rfl

/-- **A bind, forwards, needs only freshness**: every reading of the rule's made row is a reading of
the alternative the source's bind makes. -/
theorem bindValue_forward {n : ℕ} {K : List (Constraint κ Γ star)} {v : Data κ Γ star} {s : κ.Site}
    {p : Data κ Γ star} {k : Comp κ Γ star Ty} {fs : List (SourceLanguage.Frame κ Γ star Ty)}
    {ps : List (Data κ Γ star × Comp κ Γ star Ty)} (fresh : BranchBelow n ⟨K, .value v, .bindTo s p k :: fs, ps⟩)
    {σ : Assignment (fam κ) B.arity} (solved : Models σ K) (matched : instantiate σ p = instantiate σ v) :
    branchReads N ⟨K ++ [(instantiate (openAt κ s n) p, v)], .eval (k.inst (openAt κ s n)), fs, ps⟩ B
      (observe (altN N (evalN N (encComp N (instantiate σ) k)) (encStack N (instantiate σ) fs))) := by
  have vBelow : DependsBelow n v := fresh.2.1 v (by simp [focusData])
  have agree : ∀ x, Below n x → graftOpen s n σ x = σ x := fun x below => graftOpen_below σ below
  refine ⟨graftOpen s n σ, (models_append _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · intro e member
    rw [(fresh.1 e member).1 _ _ agree, (fresh.1 e member).2 _ _ agree]
    exact solved e member
  · apply (models_singleton _ _).mpr
    rw [graftOpen_open, vBelow _ _ agree]
    exact matched
  · apply congrArg observe
    simp only [encBranch, encAlt, encFocus]
    rw [encComp_mapData]
    have body : encComp N (fun t => instantiate (graftOpen s n σ) (instantiate (openAt κ s n) t)) k =
        encComp N (instantiate σ) k := by
      apply encComp_congr
      intro t _
      exact graftOpen_open s n σ t
    have rest : encStack N (instantiate (graftOpen s n σ)) fs = encStack N (instantiate σ) fs := by
      apply encStack_congr
      intro fr member t inside
      exact (fresh.2.2 fr (List.mem_cons_of_mem _ member) t inside) _ _ agree
    rw [body, rest]

/-- **A bind of a hygienic frame**: the readings of the rule's made row are exactly the readings of
the alternative the source's bind makes. -/
theorem transfer_bindValue {n : ℕ} {K : List (Constraint κ Γ star)} {v : Data κ Γ star} {s : κ.Site}
    {p : Data κ Γ star} {k : Comp κ Γ star Ty} {fs : List (SourceLanguage.Frame κ Γ star Ty)}
    {ps : List (Data κ Γ star × Comp κ Γ star Ty)} (fresh : BranchBelow n ⟨K, .value v, .bindTo s p k :: fs, ps⟩)
    (hygienic : FramePrivate s p k K v fs) (q : Observation S B.arity) :
    (∃ h : Assignment (unknownArity Γ star) B.arity,
      branchReads N ⟨K, .value v, .bindTo s p k :: fs, ps⟩ B (instantiateObservation h (bindValuePattern N)) ∧
      (Interface.Frames.contextual S).Models (a := controlFrame Γ star) (b := B) h
        (bindValueTell (Γ := Γ) (star := star)) ∧
      instantiateObservation h (bindValueMade N) = q) ↔
      branchReads N ⟨K ++ [(instantiate (openAt κ s n) p, v)], .eval (k.inst (openAt κ s n)), fs, ps⟩ B q := by
  rw [bindValue_rule_side N q]
  constructor
  · rintro ⟨σ, solved, matched, rfl⟩
    exact bindValue_forward N fresh solved matched
  · rintro ⟨σ', solved', rfl⟩
    obtain ⟨old, new⟩ := (models_append σ' _ _).mp solved'
    have bound := (models_singleton σ' _).mp new
    -- read the frame's own names as their opened copies
    let σ : Assignment (fam κ) B.arity := fun x =>
      if OwnName s p k x then σ' ⟨n :: x.scopes, x.key⟩ else σ' x
    have offOwn : ∀ x, ¬ OwnName s p k x → σ x = σ' x := fun x own => if_neg own
    obtain ⟨onStore, onValue, onFrames⟩ := hygienic σ σ' offOwn
    have onOpen : ∀ {Δ : Ctx S} {sort : S.Srt} (t : Term (signature S (fam κ)) Δ sort),
        (∀ x ∈ support t, κ.site x.key = s → OwnName s p k x) →
        instantiate σ t = instantiate σ' (instantiate (openAt κ s n) t) := by
      intro Δ sort t owns
      rw [instantiate_comp]
      apply instantiate_congr
      intro x member
      rw [openAt_eq, instantiate_generator]
      by_cases site : κ.site x.key = s
      · have own : OwnName s p k x := owns x member site
        show (if OwnName s p k x then σ' ⟨n :: x.scopes, x.key⟩ else σ' x) = _
        rw [if_pos own]
        exact read_scopes σ' (by simp [openScopes, site])
      · have notOwn : ¬ OwnName s p k x := fun own => site own.1
        show (if OwnName s p k x then σ' ⟨n :: x.scopes, x.key⟩ else σ' x) = _
        rw [if_neg notOwn]
        exact read_scopes σ' (by simp [openScopes, site])
    have onP : instantiate σ p = instantiate σ' (instantiate (openAt κ s n) p) :=
      onOpen p fun x member site => ⟨site, .inl member⟩
    have onK : encComp N (instantiate σ) k = encComp N (instantiate σ') (k.inst (openAt κ s n)) := by
      rw [encComp_mapData]
      apply encComp_congr
      intro t member
      exact onOpen t fun x inside site => ⟨site, .inr ⟨t, member, inside⟩⟩
    have onFs : encStack N (instantiate σ) fs = encStack N (instantiate σ') fs :=
      encStack_congr N fs onFrames
    refine ⟨σ, fun e member => ?_, ?_, ?_⟩
    · rw [(onStore e member).1, (onStore e member).2]
      exact old e member
    · rw [onP, onValue]
      exact bound
    · simp only [encBranch, encAlt, encFocus]
      rw [onK, onFs]

end Transfers

#print axioms graftOpen_open
#print axioms dependsBelow_open
#print axioms transfer_bindStart
#print axioms bindValue_forward
#print axioms transfer_bindValue

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
