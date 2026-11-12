import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TrueMeet

/-!
# Several parameters: what raising and the meet force, under a telescope of universe binders

Families of several parameters, `Π (x₁ : U_{p₁}) … (x_k : U_{p_k}). U_c`, compared pointwise on their domains
(`List.Forall₂` of cumulativity). Each statement is proved by induction on the binders, opening one binder at a
time, so no telescope of several fresh binders is ever built.

* `openK_typed`, `raisedK_typed`: a family opened at a smaller argument; a family η-expanded at smaller domains and a
  larger codomain.
* **`raiseK_forced`**: in `λ x̄. G x̄ ≐ λ x̄. F x̄` at `Π (x̄ : U_{p̄}). U_q`, with `p̄ ≤ p̄G ≤ p̄F` and `cF ≤ cG ≤ q`,
  every solution sends `G` to `λ x̄. F x̄` at `G`'s declaration. Each binder is opened at `U_p` and widened to
  `U_{pG}` (the tree's `equal_of_narrows`); at the end the two types are compared at `U_{cG}`
  (`universe_injective`), and η closes each binder.
* **`meetK_small`**, the meet with several parameters: with `p̄A ≤ p̄B`, `cA ≤ cB` and every `pB` below `cA`, every
  solution sends `B` to a family equal to one of `Π (x̄ : U_{p̄B}). U_{cA}`. Each binder is opened in the narrow
  telescope at `U_{pA}` and in the wide one at `U_{pB}`; the two telescopes stay a narrowing below `cA`
  (`NarrowsBelow`), and at the end the meet lemma on normal forms (`small_of_widen`) applies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate
open ContextualDependentUniverseInjective ContextualDependentCumulative

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Lists of domains -/

section Lists

variable {R : Rules Head}

/-- Every head of a list is a universe. -/
def AllUniverses (R : Rules Head) (ps : List Head) : Prop := ∀ p ∈ ps, R.isUniverse p

theorem AllUniverses.head {p : Head} {ps : List Head} (h : AllUniverses R (p :: ps)) : R.isUniverse p :=
  h p List.mem_cons_self

theorem AllUniverses.tail {p : Head} {ps : List Head} (h : AllUniverses R (p :: ps)) : AllUniverses R ps :=
  fun q member => h q (List.mem_cons_of_mem _ member)

/-- Pointwise cumulativity is transitive. -/
theorem forall₂_trans (trans : ∀ {u v w : Head}, R.cumulative u v → R.cumulative v w → R.cumulative u w)
    {l₁ l₂ l₃ : List Head} (first : List.Forall₂ R.cumulative l₁ l₂) (second : List.Forall₂ R.cumulative l₂ l₃) :
    List.Forall₂ R.cumulative l₁ l₃ := by
  induction first generalizing l₃ with
  | nil =>
      cases second
      exact .nil
  | cons h _ ih =>
      cases second with
      | cons h' t' => exact .cons (trans h h') (ih t')

/-- Pointwise related lists have one length. -/
theorem forall₂_length {l₁ l₂ : List Head} (related : List.Forall₂ R.cumulative l₁ l₂) : l₁.length = l₂.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg (· + 1) ih

/-- Heads below the heads of a list that all lie below `c` lie below `c`. -/
theorem forall₂_below (trans : ∀ {u v w : Head}, R.cumulative u v → R.cumulative v w → R.cumulative u w)
    {l₁ l₂ : List Head} (related : List.Forall₂ R.cumulative l₁ l₂) {c : Head}
    (below : ∀ p ∈ l₂, R.cumulative p c) : ∀ p ∈ l₁, R.cumulative p c := by
  induction related with
  | nil => intro p member; cases member
  | cons h _ ih =>
      intro p member
      rcases List.mem_cons.mp member with rfl | member
      · exact trans h (below _ List.mem_cons_self)
      · exact ih (fun q m => below q (List.mem_cons_of_mem _ m)) p member

/-- Pointwise cumulativity of a list with itself. -/
theorem forall₂_refl (refl : ∀ {u : Head}, R.isUniverse u → R.cumulative u u) {l : List Head}
    (universes : AllUniverses R l) : List.Forall₂ R.cumulative l l := by
  induction l with
  | nil => exact .nil
  | cons p ps ih => exact .cons (refl universes.head) (ih universes.tail)

end Lists

/-! ## Typing -/

section Typing

variable {S : Setting Head L}

/-- A β-step at the fresh variable, at any codomain: `(λ y. N) x ≡ N`. -/
theorem beta_open {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B N : Tm Head (n + 1)} {u : Head}
    (tPi : Typed S.R Γ (.pi A B) (.head u)) (hu : S.R.isUniverse u) (body : Typed S.R (.snoc Γ A) N B) :
    Equal S.R (.snoc Γ A) (.app (Presentation.rename wk (.lam N)) (.var 0)) N B := by
  have step := Derivable.betaPi (tPi.rename (CtxRen.wk Γ A)) hu (body.rename ((CtxRen.wk Γ A).snoc A))
    (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0)
  rw [Products.fresh_instantiation, Products.fresh_instantiation] at step
  exact step

/-- **A family opened at a smaller argument.** -/
theorem openK_typed {n : Nat} {Γ : Ctx Head n} {t : Tm Head n} {d p : Head} {ps : List Head} {c : Head}
    (tt : Typed S.R Γ t (famCode (p :: ps) c)) (below : S.R.cumulative d p) :
    Typed S.R (.snoc Γ (.head d)) (.app (Presentation.rename wk t) (.var 0)) (famCode ps c) := by
  have weak := tt.rename (CtxRen.wk Γ (.head d))
  rw [famCode_rename] at weak
  have step := Derivable.appElim weak (Derivable.cumul (var_head_typed Γ d) below)
  simpa only [inst0, famCode_subst] using step

/-- **A family η-expanded at smaller domains and a larger codomain.** -/
theorem raisedK_typed : ∀ {psG psF : List Head}, List.Forall₂ S.R.cumulative psG psF →
    ∀ {n : Nat} {Γ : Ctx Head n} {t : Tm Head n} {cF c : Head}, AllUniverses S.R psG → S.R.isUniverse c →
      S.R.cumulative cF c → CtxFormed S.R Γ → Typed S.R Γ t (famCode psF cF) →
      Typed S.R Γ (etaExp psG.length t) (famCode psG c) := by
  intro psG psF domains
  induction domains with
  | nil =>
      intro n Γ t cF c _ _ codomain _ tt
      exact Derivable.cumul tt codomain
  | @cons pG pF psG' psF' head _ ih =>
      intro n Γ t cF c universes hc codomain formed tt
      have formed' : CtxFormed S.R (.snoc Γ (.head pG)) := formed.snoc (IsType.head_of_universe universes.head)
      have inner := ih universes.tail hc codomain formed' (openK_typed tt head)
      obtain ⟨u, hu, tPi⟩ := famCode_isType (pG :: psG') universes hc formed
      have tPi' : Typed S.R Γ (.pi (.head pG) (famCode psG' c)) (.head u) := tPi
      exact Derivable.lamIntro tPi' hu inner

end Typing

/-! ## What the equations force -/

section Forcing

variable {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **What raising forces, with several parameters**: two families whose η-expansions are equal at the annotation
`Π (x̄ : U_{p̄}). U_q` are equal at the larger one's declaration, the other η-expanded. -/
theorem raiseK_forced : ∀ {ps psG : List Head}, List.Forall₂ S.R.cumulative ps psG →
    ∀ {psF : List Head}, List.Forall₂ S.R.cumulative psG psF →
    ∀ {n : Nat} {Δ : Ctx Head n} {g f : Tm Head n} {cG cF q : Head},
      AllUniverses S.R ps → AllUniverses S.R psG → S.R.isUniverse cG → S.R.isUniverse cF → S.R.isUniverse q →
      S.R.cumulative cF cG → S.R.cumulative cG q → CtxFormed S.R Δ →
      Typed S.R Δ g (famCode psG cG) → Typed S.R Δ f (famCode psF cF) →
      Equal S.R Δ (etaExp ps.length g) (etaExp ps.length f) (famCode ps q) →
      Equal S.R Δ g (etaExp psG.length f) (famCode psG cG) := by
  intro ps psG annotation
  induction annotation with
  | nil =>
      intro psF fits n Δ g f cG cF q _ _ hcG _ hq codomainF _ formed tg tf equal
      cases fits
      exact universe_injective facts roots heads algebra rigid complete formed hcG hq tg
        (Derivable.cumul tf codomainF) equal
  | @cons p pG ps' psG' below rest ih =>
      intro psF fits n Δ g f cG cF q univ univG hcG hcF hq codomainF codomainG formed tg tf equal
      cases fits with
      | @cons _ pF _ psF' belowF restF =>
          have hp := univ.head
          have hpG := univG.head
          have codomainFq := algebra.trans codomainF codomainG
          have restPF := forall₂_trans algebra.trans rest restF
          have formedP : CtxFormed S.R (.snoc Δ (.head p)) := formed.snoc (IsType.head_of_universe hp)
          have formedG : CtxFormed S.R (.snoc Δ (.head pG)) := formed.snoc (IsType.head_of_universe hpG)
          change Equal S.R Δ (.lam (etaExp ps'.length (.app (Presentation.rename wk g) (.var 0))))
            (.lam (etaExp ps'.length (.app (Presentation.rename wk f) (.var 0)))) (.pi (.head p) (famCode ps' q))
            at equal
          -- Open the equation at `x : U_p`.
          have opened := equal_of_lam_left facts formed equal
          have fBodyP := raisedK_typed restPF univ.tail hq codomainFq formedP
            (openK_typed tf (algebra.trans below belowF))
          obtain ⟨uP, huP, tPiP⟩ := famCode_isType (p :: ps') univ hq formed
          have narrowEq := opened.trans (beta_open tPiP huP fBodyP)
          -- Widen it to `x : U_{pG}`.
          have gOpen := openK_typed tg (S.levels.cumulative_refl hpG)
          have fOpen := openK_typed tf belowF
          have wide := equal_of_narrows facts roots heads algebra rigid complete
            (.lower (CtxNarrows.refl Δ) below) formedG formedP
            (raisedK_typed rest univ.tail hq codomainG formedG gOpen)
            (raisedK_typed restPF univ.tail hq codomainFq formedG fOpen) narrowEq
          -- Inside, then η at `G`'s declaration.
          have inner := ih restF univ.tail univG.tail hcG hcF hq codomainF codomainG formedG gOpen fOpen wide
          have tEta := raisedK_typed (.cons belowF restF) univG hcG codomainF formed tf
          obtain ⟨uG, huG, tPiG⟩ := famCode_isType (pG :: psG') univG hcG formed
          have betaG := beta_open tPiG huG (raisedK_typed restF univG.tail hcG codomainF formedG fOpen)
          exact Derivable.etaPi tg tEta (inner.trans betaG.symm)

include facts roots heads algebra rigid complete in
/-- **The meet with several parameters**: a family `a` of `Π (x̄ : U_{p̄A}). U_{cA}` over a narrowing `N` below `cA`,
and a family `b` of `Π (x̄ : U_{p̄B}). U_{cB}` over the wide telescope `W`, whose η-expansions are equal over `N` at
`Π (x̄ : U_{p̄}). U_q`: then `b` is equal over `W` to a family of the meet `Π (x̄ : U_{p̄B}). U_{cA}`. -/
theorem meetK_small {cA cB q : Head} (hcA : S.R.isUniverse cA) (hcB : S.R.isUniverse cB) (hq : S.R.isUniverse q)
    (codomainA : S.R.cumulative cA q) (codomainB : S.R.cumulative cB q) (codomain : S.R.cumulative cA cB) :
    ∀ {ps psA : List Head}, List.Forall₂ S.R.cumulative ps psA →
    ∀ {psB : List Head}, List.Forall₂ S.R.cumulative psA psB →
      AllUniverses S.R ps → AllUniverses S.R psA → AllUniverses S.R psB → (∀ p ∈ psB, S.R.cumulative p cA) →
      ∀ {n : Nat} {W N : Ctx Head n}, NarrowsBelow S.R cA W N → CtxFormed S.R W → CtxFormed S.R N →
      ∀ {a b : Tm Head n}, Typed S.R N a (famCode psA cA) → Typed S.R W b (famCode psB cB) →
        Equal S.R N (etaExp ps.length a) (etaExp ps.length b) (famCode ps q) →
        ∃ h, Typed S.R W h (famCode psB cA) ∧ Equal S.R W b h (famCode psB cB) := by
  intro ps psA annotation
  induction annotation with
  | nil =>
      intro psB domains _ _ _ _ n W N nb formedW formedN a b ta tb equal
      cases domains
      exact small_of_widen facts roots heads algebra rigid complete hcA hcB nb formedW formedN tb ta ⟨q, hq, equal⟩
  | @cons p pA ps' psA' below rest ih =>
      intro psB domains univ univA univB crossing n W N nb formedW formedN a b ta tb equal
      cases domains with
      | @cons _ pB _ psB' belowB restB =>
          have hp := univ.head
          have hpA := univA.head
          have hpB := univB.head
          have restPB := forall₂_trans algebra.trans rest restB
          have tbN : Typed S.R N b (famCode (pB :: psB') cB) := typed_narrow nb.narrows tb
          have formedNP : CtxFormed S.R (.snoc N (.head p)) := formedN.snoc (IsType.head_of_universe hp)
          have formedNA : CtxFormed S.R (.snoc N (.head pA)) := formedN.snoc (IsType.head_of_universe hpA)
          have formedWB : CtxFormed S.R (.snoc W (.head pB)) := formedW.snoc (IsType.head_of_universe hpB)
          change Equal S.R N (.lam (etaExp ps'.length (.app (Presentation.rename wk a) (.var 0))))
            (.lam (etaExp ps'.length (.app (Presentation.rename wk b) (.var 0)))) (.pi (.head p) (famCode ps' q))
            at equal
          -- Open the equation at `x : U_p` in the narrow telescope.
          have opened := equal_of_lam_left facts formedN equal
          have bBodyP := raisedK_typed restPB univ.tail hq codomainB formedNP
            (openK_typed tbN (algebra.trans below belowB))
          obtain ⟨uP, huP, tPiP⟩ := famCode_isType (p :: ps') univ hq formedN
          have narrowEq := opened.trans (beta_open tPiP huP bBodyP)
          -- Widen it to `x : U_{pA}` in the narrow telescope.
          have aOpen := openK_typed ta (S.levels.cumulative_refl hpA)
          have wide := equal_of_narrows facts roots heads algebra rigid complete
            (.lower (CtxNarrows.refl N) below) formedNA formedNP
            (raisedK_typed rest univ.tail hq codomainA formedNA aOpen)
            (raisedK_typed restPB univ.tail hq codomainB formedNA (openK_typed tbN belowB)) narrowEq
          -- Inside: the binder at `U_{pA}` in the narrow telescope and at `U_{pB}` in the wide one.
          have nb' : NarrowsBelow S.R cA (.snoc W (.head pB)) (.snoc N (.head pA)) :=
            .lower nb belowB (crossing pB List.mem_cons_self)
          obtain ⟨h', th', eh'⟩ := ih restB univ.tail univA.tail univB.tail
            (fun x member => crossing x (List.mem_cons_of_mem _ member)) nb' formedWB formedNA aOpen
            (openK_typed tb (S.levels.cumulative_refl hpB)) wide
          -- The family of the meet, `λ x. h'`.
          obtain ⟨uM, huM, tPiM⟩ := famCode_isType (pB :: psB') univB hcA formedW
          have tPiM' : Typed S.R W (.pi (.head pB) (famCode psB' cA)) (.head uM) := tPiM
          refine ⟨.lam h', Derivable.lamIntro tPiM' huM th', ?_⟩
          -- η at `B`'s declaration.
          obtain ⟨uB, huB, tPiB⟩ := famCode_isType (pB :: psB') univB hcB formedW
          have tPiB' : Typed S.R W (.pi (.head pB) (famCode psB' cB)) (.head uB) := tPiB
          have th'B : Typed S.R (.snoc W (.head pB)) h' (famCode psB' cB) :=
            .sub th' ((lowers_famCode psB' hcA hcB codomain).usable
              (famCode_isType psB' univB.tail hcA formedWB) (famCode_isType psB' univB.tail hcB formedWB))
          have tLam : Typed S.R W (.lam h') (.pi (.head pB) (famCode psB' cB)) := Derivable.lamIntro tPiB' huB th'B
          exact Derivable.etaPi tb tLam (eh'.trans (beta_open tPiB' huB th'B).symm)

end Forcing

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
