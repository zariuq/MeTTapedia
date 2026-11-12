import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinSolver

/-!
# The join with a meet: domains in any order, codomains comparable

At `λ x̄. F x̄ ≐ λ x̄. G x̄`, with `F : Π (x̄ : U_{p̄F}). U_{cF}` and `G : Π (x̄ : U_{p̄G}). U_{cG}`, `cF` below `cG`:
`G` is declared again at `Π (x̄ : U_{p̄J}). U_{cF}`, with `p̄J` least upper bounds of the domains, and both unknowns are
sent to its η-expansion. The rule is exact (`joinMeetK_exact`) under **the crossing** (`CrossesK`): at each position
the joined domain is `F`'s own, or lies below `F`'s codomain.

The comparable cases of the rules of meet groups are instances: when `G`'s domains lie below `F`'s, every joined domain
is `F`'s own and the crossing holds with nothing to check (domain raising); when `F`'s domains lie below `G`'s, the
crossing asks that `G`'s domains lie below `cF` (the true meet). The cross store (`X : U0 → U0`, `Y : U1 → U1` at
`U0 → U1`) fails the crossing and has no principal answer.

**What the crossing buys** (`join_body_meet`): the common normal body of a solution is a type of `U_{cG}` over the join
of the two telescopes; over `F`'s telescope it is a type of `U_{cF}`, and the crossing makes `F`'s telescope a
narrowing of the join below `cF`, so the body is a type of `U_{cF}` over the join (`typed_widen`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective ContextualDependentCumulative ContextualDependentEtaLong

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-- **The crossing, position by position**: the joined domain is `F`'s own, or lies below `c`. -/
inductive CrossesK (R : Rules Head) (c : Head) : List Head → List Head → Prop where
  | nil : CrossesK R c [] []
  | keep {p : Head} {ps ws : List Head} : CrossesK R c ps ws → CrossesK R c (p :: ps) (p :: ws)
  | lower {p w : Head} {ps ws : List Head} : R.cumulative w c → CrossesK R c ps ws → CrossesK R c (p :: ps) (w :: ws)

section Forcing

variable {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')

include facts roots heads algebra rigid complete headsTyped in
/-- **The join of two bodies of comparable universes**: types of `U_{cF}` over `F` and of `U_{cG}` over `G`, equal over
a common narrowing, are equal to one type of `U_{cF}` over the join, when `F` narrows the join below `cF`. -/
theorem join_body_meet {n : Nat} {A F G J : Ctx Head n} {cF cG q : Head} (nF : CtxNarrows S.R F A)
    (nG : CtxNarrows S.R G A) (j : JoinOf S.R F G J) (nb : NarrowsBelow S.R cF J F) (formedA : CtxFormed S.R A)
    (formedF : CtxFormed S.R F) (formedG : CtxFormed S.R G) (formedJ : CtxFormed S.R J) {f g : Tm Head n}
    (hcF : S.R.isUniverse cF) (hcG : S.R.isUniverse cG) (hq : S.R.isUniverse q) (cFG : S.R.cumulative cF cG)
    (cGq : S.R.cumulative cG q) (tf : Typed S.R F f (.head cF)) (tg : Typed S.R G g (.head cG))
    (equal : Equal S.R A f g (.head q)) :
    ∃ Z, Typed S.R J Z (.head cF) ∧ Equal S.R F f Z (.head cF) ∧ Equal S.R G g Z (.head cG) := by
  obtain ⟨Zf, lZf, atZf⟩ := long_type_exists facts roots heads algebra rigid complete formedF ⟨cF, hcF, tf⟩
  obtain ⟨tZf, eZf⟩ := atZf hcF tf
  obtain ⟨Zg, lZg, atZg⟩ := long_type_exists facts roots heads algebra rigid complete formedG ⟨cG, hcG, tg⟩
  obtain ⟨tZg, eZg⟩ := atZg hcG tg
  have lZfA := Long.type_narrow facts lZf nF formedF formedA
  have lZgA := Long.type_narrow facts lZg nG formedG formedA
  have eA : TypeEq S.R A Zg Zf :=
    ⟨q, hq, (Derivable.cumulEq (equal_narrow nG eZg) cGq).symm.trans
      (equal.symm.trans (Derivable.cumulEq (equal_narrow nF eZf) (algebra.trans cFG cGq)))⟩
  have same := long_type_unique facts roots heads algebra complete formedA lZgA lZfA eA
  have eG : Equal S.R G Zg Zf (.head cG) := Long.sameEqual facts heads lZg formedG same hcG tZg
  have tZfG : Typed S.R G Zf (.head cG) := (Equal.typed eG formedG).2
  -- The join, at the larger codomain.
  have tJ := typed_join facts roots heads algebra rigid complete headsTyped j formedF formedG formedJ
    (long_type_normal rigid lZf) (Derivable.cumul tZf cFG) tZfG (IsType.head_of_universe hcG)
  -- Its η-long form over the join is a type of the smaller codomain there.
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formedJ ⟨cG, hcG, tJ⟩
  obtain ⟨_, eZ⟩ := atZ hcG tJ
  have lZF := Long.type_narrow facts lZ nb.narrows formedJ formedF
  have eZF : Equal S.R F Zf Z (.head cG) := equal_narrow nb.narrows eZ
  have tZF : Typed S.R F Z (.head cF) :=
    normal_typed_of_equal facts roots heads algebra rigid complete formedF hcF tZf ⟨cG, hcG, eZF⟩ lZF
  have tZJ : Typed S.R J Z (.head cF) := typed_widen facts algebra Z hcF nb formedJ formedF lZ tZF
  have eZF' : Equal S.R F Zf Z (.head cF) :=
    universe_injective facts roots heads algebra rigid complete formedF hcF hcG tZf tZF eZF
  have eZG : Equal S.R G Zf Z (.head cG) := equal_narrow j.narrows_right eZ
  exact ⟨Z, tZJ, eZf.trans eZF', eZg.trans (eG.trans eZG)⟩

include facts roots heads algebra rigid complete headsTyped in
/-- **What the join with a meet forces, under the binders.** -/
theorem joinMeetK_open : ∀ {ps psF : List Head}, List.Forall₂ S.R.cumulative ps psF →
    ∀ {psG : List Head}, List.Forall₂ S.R.cumulative ps psG → ∀ {psJ : List Head}, JoinsK S.R psF psG psJ →
    ∀ {cF : Head}, CrossesK S.R cF psF psJ →
    ∀ {n : Nat} {A F G J : Ctx Head n}, CtxNarrows S.R F A → CtxNarrows S.R G A → JoinOf S.R F G J →
      NarrowsBelow S.R cF J F → CtxFormed S.R A → CtxFormed S.R F → CtxFormed S.R G → CtxFormed S.R J →
      ∀ {f g : Tm Head n} {cG q : Head}, AllUniverses S.R ps → AllUniverses S.R psF → AllUniverses S.R psG →
      S.R.isUniverse cF → S.R.isUniverse cG → S.R.isUniverse q → S.R.cumulative cF cG → S.R.cumulative cG q →
      Typed S.R F f (famCode psF cF) → Typed S.R G g (famCode psG cG) →
      Equal S.R A (etaExp ps.length f) (etaExp ps.length g) (famCode ps q) →
      ∃ h, Typed S.R J h (famCode psJ cF) ∧ Equal S.R F f (etaExp psF.length h) (famCode psF cF) ∧
        Equal S.R G g (etaExp psG.length h) (famCode psG cG) := by
  intro ps psF annF
  induction annF with
  | nil =>
      intro psG annG psJ joins cF _ n A F G J nF nG j nb formedA formedF formedG formedJ f g cG q _ _ _ hcF hcG hq
        cFG cGq tf tg equal
      cases annG
      cases joins
      exact join_body_meet facts roots heads algebra rigid complete headsTyped nF nG j nb formedA formedF formedG
        formedJ hcF hcG hq cFG cGq tf tg equal
  | @cons p pF ps' psF' belowF restF ih =>
      intro psG annG psJ joins cF crosses n A F G J nF nG j nb formedA formedF formedG formedJ f g cG q univ univF
        univG hcF hcG hq cFG cGq tf tg equal
      cases annG with
      | @cons _ pG _ psG' belowG restG =>
          cases joins with
          | @cons _ _ pJ _ _ psJ' hpJ lub restJ =>
              have step : NarrowsBelow S.R cF (.snoc J (.head pJ)) (.snoc F (.head pF)) ∧
                  CrossesK S.R cF psF' psJ' := by
                cases crosses with
                | keep restC => exact ⟨.same _ nb, restC⟩
                | lower below restC => exact ⟨.lower nb lub.1 below, restC⟩
              obtain ⟨nb', restC⟩ := step
              have hp := univ.head
              have hpF := univF.head
              have hpG := univG.head
              have univJ : AllUniverses S.R (pJ :: psJ') := JoinsK.universes (.cons hpJ lub restJ)
              have formedA' : CtxFormed S.R (.snoc A (.head p)) := formedA.snoc (IsType.head_of_universe hp)
              have formedF' : CtxFormed S.R (.snoc F (.head pF)) := formedF.snoc (IsType.head_of_universe hpF)
              have formedG' : CtxFormed S.R (.snoc G (.head pG)) := formedG.snoc (IsType.head_of_universe hpG)
              have formedJ' : CtxFormed S.R (.snoc J (.head pJ)) := formedJ.snoc (IsType.head_of_universe hpJ)
              change Equal S.R A (.lam (etaExp ps'.length (.app (Presentation.rename wk f) (.var 0))))
                (.lam (etaExp ps'.length (.app (Presentation.rename wk g) (.var 0)))) (.pi (.head p) (famCode ps' q))
                at equal
              -- Open the equation at `x : U_p` over the annotation's telescope.
              have opened := equal_of_lam_left facts formedA equal
              have tgA : Typed S.R A g (famCode (pG :: psG') cG) := typed_narrow nG tg
              have gBody := raisedK_typed restG univ.tail hq cGq formedA' (openK_typed tgA belowG)
              obtain ⟨uP, huP, tPiP⟩ := famCode_isType (p :: ps') univ hq formedA
              have tPiP' : Typed S.R A (.pi (.head p) (famCode ps' q)) (.head uP) := tPiP
              have narrowEq := opened.trans (beta_open tPiP' huP gBody)
              -- The induction, over the four telescopes extended by their binders.
              obtain ⟨h', th', eF', eG'⟩ := ih restG restJ restC (.lower nF belowF) (.lower nG belowG)
                (.join j hpF hpG hpJ lub) nb' formedA' formedF' formedG' formedJ' univ.tail univF.tail univG.tail
                hcF hcG hq cFG cGq (openK_typed tf (S.levels.cumulative_refl hpF))
                (openK_typed tg (S.levels.cumulative_refl hpG)) narrowEq
              -- The family `λ x. h'`, of the smaller codomain.
              obtain ⟨uJ, huJ, tPiJ⟩ := famCode_isType (pJ :: psJ') univJ hcF formedJ
              have tPiJ' : Typed S.R J (.pi (.head pJ) (famCode psJ' cF)) (.head uJ) := tPiJ
              have th : Typed S.R J (.lam h') (famCode (pJ :: psJ') cF) := Derivable.lamIntro tPiJ' huJ th'
              refine ⟨.lam h', th, ?_, ?_⟩
              · exact eta_join_side facts j.narrows_left formedF lub.1 restJ.left univF univJ hcF hcF
                  (S.levels.cumulative_refl hcF) tf th eF'
              · exact eta_join_side facts j.narrows_right formedG lub.2.1 restJ.right univG univJ hcG hcF cFG tg th
                  eG'

include facts roots heads algebra rigid complete headsTyped in
/-- **What the join with a meet forces at a flex–flex equation**: with `cl` below `cr` and the crossing, every
solution sends both unknowns to η-expansions of one family of `Π (x̄ : U_{p̄J}). U_{cl}`. -/
theorem joinMeetK_forces {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e)
    (low : S.R.cumulative v.cl v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ)
    (crosses : CrossesK S.R v.cl v.psl psJ) : JoinForces v psJ v.cl := by
  intro Δ f solved
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code)
    (Presentation.subst f.substitution e.2.2.code) (Presentation.subst f.substitution e.1.1.code) at equal
  rw [v.side_left, v.side_right, v.annotation_left, subst_etaExp, subst_etaExp, famCode_subst] at equal
  have tF : Typed S.R Δ.raw (f.substitution v.left) (famCode v.psl v.cl) := by
    have typed := f.typed v.left
    rw [v.declared_left, famCode_subst] at typed
    exact typed
  have tG : Typed S.R Δ.raw (f.substitution v.right) (famCode v.psr v.cr) := by
    have typed := f.typed v.right
    rw [v.declared_right, famCode_subst] at typed
    exact typed
  exact joinMeetK_open facts roots heads algebra rigid complete headsTyped v.domain_left v.domain_right joins crosses
    (CtxNarrows.refl Δ.raw) (CtxNarrows.refl Δ.raw) (JoinOf.refl S.R Δ.raw) (NarrowsBelow.refl v.cl Δ.raw) Δ.formed
    Δ.formed Δ.formed Δ.formed v.universes v.universes_left v.universes_right v.universe_cl v.universe_cr
    v.universe_q low v.codomain_right tF tG equal

include facts roots heads algebra rigid complete headsTyped in
/-- **The join with a meet is exact**: `G` declared again at `Π (x̄ : U_{p̄J}). U_{cl}`, both unknowns sent to its
η-expansion. -/
theorem joinMeetK_exact {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    (low : S.R.cumulative v.cl v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ)
    (crosses : CrossesK S.R v.cl v.psl psJ) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest)
      (joinMKHom Θ families v joins v.universe_cl (S.levels.cumulative_refl v.universe_cl) low)
      ((frames S.levels).applyStore
        (joinMKHom Θ families v joins v.universe_cl (S.levels.cumulative_refl v.universe_cl) low) rest) :=
  joinMK_exact families v joins v.universe_cl _ low
    (joinMeetK_forces facts roots heads algebra rigid complete headsTyped v low joins crosses) rest

include facts roots heads algebra rigid complete headsTyped in
/-- **The join with a meet on a whole store**: the other equations are transported and their sides of `F` and `G`
re-read as sides of the redeclared unknown; exact. -/
theorem joinMeetRereadK_exact [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
    [DecidableRel S.R.cumulative] {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)}
    (v : FlexK e) (low : S.R.cumulative v.cl v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ)
    (crosses : CrossesK S.R v.cl v.psl psJ) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest)
      (joinMKHom Θ families v joins v.universe_cl (S.levels.cumulative_refl v.universe_cl) low)
      (joinStore families v joins v.universe_cl (S.levels.cumulative_refl v.universe_cl) low rest) :=
  joinRereadK_exact families v joins v.universe_cl _ low
    (joinMeetK_forces facts roots heads algebra rigid complete headsTyped v low joins crosses) rest

end Forcing

/-! ## The comparable cases -/

section Comparable

variable {S : Setting Head L}

/-- **Domain raising is an instance**: when `G`'s domains lie below `F`'s, `F`'s own domains are least upper bounds,
and the crossing keeps every position (`crossesK_keep_all`). -/
theorem joins_of_below : ∀ {psF psG : List Head}, List.Forall₂ S.R.cumulative psG psF → AllUniverses S.R psF →
    JoinsK S.R psF psG psF := by
  intro psF psG below
  induction below with
  | nil => intro _; exact .nil
  | @cons pG pF psG' psF' le _ ih =>
      intro universes
      exact .cons universes.head (isLub_left universes.head le) (ih universes.tail)

/-- The crossing that keeps every position holds below every universe. -/
theorem crossesK_keep_all (c : Head) : ∀ (ps : List Head), CrossesK S.R c ps ps
  | [] => .nil
  | _ :: ps => .keep (crossesK_keep_all c ps)

/-- **The true meet is an instance**: when `F`'s domains lie below `G`'s and below `cF`'s bound, `G`'s domains are least
upper bounds and the crossing holds. -/
theorem joins_of_above : ∀ {psF psG : List Head}, List.Forall₂ S.R.cumulative psF psG → AllUniverses S.R psG →
    ∀ {c : Head}, (∀ p ∈ psG, S.R.cumulative p c) → JoinsK S.R psF psG psG ∧ CrossesK S.R c psF psG := by
  intro psF psG below
  induction below with
  | nil => intro _ _ _; exact ⟨.nil, .nil⟩
  | @cons pF pG psF' psG' le _ ih =>
      intro universes c bounded
      obtain ⟨joins, crosses⟩ := ih universes.tail (fun p member => bounded p (List.mem_cons_of_mem _ member))
      exact ⟨.cons universes.head (isLub_right universes.head le) joins,
        .lower (bounded pG List.mem_cons_self) crosses⟩

end Comparable

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
