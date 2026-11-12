import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinMeetSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbMeet

/-!
# The glb join: incomparable codomains together with incomparable domains

At `λ x̄. F x̄ ≐ λ x̄. G x̄`, with `F : Π (x̄ : U_{p̄F}). U_{cF}` and `G : Π (x̄ : U_{p̄G}). U_{cG}`, neither the domains nor
the codomains need be comparable. The rule declares `G` again at `Π (x̄ : U_{p̄J}). U_g`, with `p̄J` least upper bounds
of the domains and `g` a greatest lower bound of the codomains, and sends both unknowns to its η-expansion
(`joinMKHom`). It is one rule: the greatest-lower-bound lowering and the join widening at once.

**The condition** (`CrossAt`), position by position: a position whose domain lies below its own codomain on both sides
has each domain below the other side's codomain too. It reads no join and no meet.

* **The joint widening** (`typed_widen_both`): a normal type of the join telescope that is a type of `U_a` over the
  first telescope and of `U_b` over the second is a type of `U_a` over the join, when each widened position lies below
  `a` as soon as its two declarations lie below `a` and `b`. A widened declaration enters a normal type only through its
  variable at a type position, and there both typings bound it.
* **What the equation forces** (`glbJoinK_forces`): every solution sends `F` and `G` to η-expansions of one family of
  `Π (x̄ : U_{p̄J}). U_g`. The common body is a type over the join at the annotation's codomain (`typed_join`), of `U_cF`
  and of `U_cG` there by the joint widening, hence of `U_g` by its least universe (`least_universe`).
* **The rule is exact** (`glbJoinK_exact`, and with re-reading `glbJoinRereadK_exact`).
* **The condition is exactly what positions used as types need**: the join with a meet's crossing implies it
  (`crossAt_of_crossOK`), and so does one codomain (`crossAt_same`); a position whose domain exceeds its codomain
  satisfies it vacuously, where the crossing fails.
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

/-! ## The condition -/

section Condition

/-- **A position usable on both sides lies below both codomains**: when `p` lies below `c` and `p'` below `c'`, then
`p` lies below `c'` and `p'` below `c`. -/
def CrossAt (R : Rules Head) (c c' p p' : Head) : Prop :=
  R.cumulative p c → R.cumulative p' c' → R.cumulative p c' ∧ R.cumulative p' c

instance (R : Rules Head) [DecidableRel R.cumulative] (c c' p p' : Head) : Decidable (CrossAt R c c' p p') := by
  unfold CrossAt
  infer_instance

theorem CrossAt.symm {R : Rules Head} {c c' p p' : Head} (h : CrossAt R c c' p p') : CrossAt R c' c p' p :=
  fun hp' hp => (h hp hp').symm

theorem crossAt_forall₂_symm {R : Rules Head} {c c' : Head} :
    ∀ {ps ps' : List Head}, List.Forall₂ (CrossAt R c c') ps ps' → List.Forall₂ (CrossAt R c' c) ps' ps
  | _, _, .nil => .nil
  | _, _, .cons h rest => .cons h.symm (crossAt_forall₂_symm rest)

/-- With one codomain every position crosses. -/
theorem crossAt_same (R : Rules Head) (c p p' : Head) : CrossAt R c c p p' := fun hp hp' => ⟨hp, hp'⟩

/-- Lists of one length, with one codomain, cross at every position. -/
theorem crossAt_same_all (R : Rules Head) (c : Head) :
    ∀ {ps ps' : List Head}, ps.length = ps'.length → List.Forall₂ (CrossAt R c c) ps ps'
  | [], [], _ => .nil
  | _ :: _, _ :: _, lengths => .cons (crossAt_same R c _ _) (crossAt_same_all R c (Nat.succ.inj lengths))
  | [], _ :: _, lengths => by cases lengths
  | _ :: _, [], lengths => by cases lengths

/-- **The join with a meet's crossing implies the condition**: with `c` below `c'`, at a position where `p'` lies below
`p` or both lie below `c`. -/
theorem crossAt_of_crossOK {R : Rules Head} (trans : ∀ {u v w : Head}, R.cumulative u v → R.cumulative v w →
    R.cumulative u w) {c c' : Head} (le : R.cumulative c c') :
    ∀ {ps ps' : List Head}, CrossOK R c ps ps' → List.Forall₂ (CrossAt R c c') ps ps'
  | _, _, .nil => .nil
  | _, _, .cons here rest =>
      .cons (fun hp _ => ⟨trans hp le, by rcases here with below | ⟨_, below⟩; exacts [trans below hp, below]⟩)
        (crossAt_of_crossOK trans le rest)

end Condition

/-! ## The joint widening -/

section Widening

/-- **`J` widens `F` toward `a`, given `G` at `b`**: the three telescopes agree except at universe declarations, where
`J` declares a universe above `F`'s and `G`'s that lies below `a` whenever `F`'s lies below `a` and `G`'s below `b`. -/
inductive WidensBoth (R : Rules Head) (a b : Head) : {n : Nat} → Ctx Head n → Ctx Head n → Ctx Head n → Prop where
  | nil : WidensBoth R a b .nil .nil .nil
  | same {n : Nat} {J F G : Ctx Head n} (A : Tm Head n) : WidensBoth R a b J F G →
      WidensBoth R a b (.snoc J A) (.snoc F A) (.snoc G A)
  | lower {n : Nat} {J F G : Ctx Head n} {w vF vG : Head} : WidensBoth R a b J F G → R.isUniverse w →
      R.isUniverse vF → R.isUniverse vG → R.cumulative vF w → R.cumulative vG w →
      (R.cumulative vF a → R.cumulative vG b → R.cumulative w a) →
      WidensBoth R a b (.snoc J (.head w)) (.snoc F (.head vF)) (.snoc G (.head vG))

variable {R : Rules Head}

/-- Every telescope widens itself. -/
theorem WidensBoth.refl (a b : Head) : ∀ {n : Nat} (Γ : Ctx Head n), WidensBoth R a b Γ Γ Γ
  | _, .nil => .nil
  | _, .snoc Γ A => .same A (WidensBoth.refl a b Γ)

theorem WidensBoth.narrows_left {a b : Head} {n : Nat} {J F G : Ctx Head n} (wb : WidensBoth R a b J F G) :
    CtxNarrows R J F := by
  induction wb with
  | nil => exact .nil
  | same A _ ih => exact .same A ih
  | lower _ _ _ _ cF _ _ ih => exact .lower ih cF

theorem WidensBoth.narrows_right {a b : Head} {n : Nat} {J F G : Ctx Head n} (wb : WidensBoth R a b J F G) :
    CtxNarrows R J G := by
  induction wb with
  | nil => exact .nil
  | same A _ ih => exact .same A ih
  | lower _ _ _ _ _ cG _ ih => exact .lower ih cG

/-- **A declaration of the widened telescope** is the common one, or a universe as in the definition. -/
theorem WidensBoth.lookup {a b : Head} {n : Nat} {J F G : Ctx Head n} (wb : WidensBoth R a b J F G) :
    ∀ i, (Ctx.lookup F i = Ctx.lookup J i ∧ Ctx.lookup G i = Ctx.lookup J i) ∨
      ∃ w vF vG, Ctx.lookup J i = .head w ∧ Ctx.lookup F i = .head vF ∧ Ctx.lookup G i = .head vG ∧
        R.isUniverse w ∧ R.isUniverse vF ∧ R.isUniverse vG ∧ (R.cumulative vF a → R.cumulative vG b → R.cumulative w a) := by
  induction wb with
  | nil => intro i; exact i.elim0
  | same A _ ih =>
      intro i
      refine Fin.cases (.inl ⟨rfl, rfl⟩) (fun k => ?_) i
      rw [Ctx.lookup_snoc_succ, Ctx.lookup_snoc_succ, Ctx.lookup_snoc_succ]
      rcases ih k with ⟨eF, eG⟩ | ⟨w, vF, vG, eJ, eF, eG, hw, hvF, hvG, below⟩
      · exact .inl ⟨by rw [eF], by rw [eG]⟩
      · exact .inr ⟨w, vF, vG, by rw [eJ]; rfl, by rw [eF]; rfl, by rw [eG]; rfl, hw, hvF, hvG, below⟩
  | lower _ hw hvF hvG _ _ below ih =>
      intro i
      refine Fin.cases (.inr ⟨_, _, _, rfl, rfl, rfl, hw, hvF, hvG, below⟩) (fun k => ?_) i
      rw [Ctx.lookup_snoc_succ, Ctx.lookup_snoc_succ, Ctx.lookup_snoc_succ]
      rcases ih k with ⟨eF, eG⟩ | ⟨w', vF', vG', eJ, eF, eG, hw', hvF', hvG', below'⟩
      · exact .inl ⟨by rw [eF], by rw [eG]⟩
      · exact .inr ⟨w', vF', vG', by rw [eJ]; rfl, by rw [eF]; rfl, by rw [eG]; rfl, hw', hvF', hvG', below'⟩

variable {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (algebra : CumulativeAlgebra S.R)

include facts algebra in
/-- **The joint widening**: a normal type of `J` that is a type of `U_a` over `F` and of `U_b` over `G` is a type of
`U_a` over `J`. -/
theorem typed_widen_both : ∀ {n : Nat} (V : Tm Head n) {J F G : Ctx Head n} {a b : Head}, S.R.isUniverse a →
    S.R.isUniverse b → WidensBoth S.R a b J F G → CtxFormed S.R J → CtxFormed S.R F → CtxFormed S.R G →
    Long S.R S.roles (.type J V) → Typed S.R F V (.head a) → Typed S.R G V (.head b) → Typed S.R J V (.head a) := by
  intro n V
  induction V with
  | var i =>
      intro J F G a b ha hb wb formedJ formedF formedG long smallF smallG
      cases long with
      | neutralType ls htop le =>
          cases ls with
          | var _ e =>
              rcases wb.lookup i with ⟨sameF, _⟩ | ⟨w, vF, vG, eJ, eF, eG, _, hvF, hvG, below⟩
              · exact spine_small_wide facts algebra wb.narrows_left formedJ formedF (.var i e)
                  (.var i (by rw [sameF]; exact typeEq_narrow wb.narrows_left e)) htop le smallF
              · have cF : S.R.cumulative vF a := by
                  have generation : TypeLe S.R F (Ctx.lookup F i) (.head a) := Typed.generation smallF
                  rw [eF] at generation
                  exact typeLe_head_cumulative facts algebra formedF hvF ha generation
                have cG : S.R.cumulative vG b := by
                  have generation : TypeLe S.R G (Ctx.lookup G i) (.head b) := Typed.generation smallG
                  rw [eG] at generation
                  exact typeLe_head_cumulative facts algebra formedG hvG hb generation
                have typed : Typed S.R J (.var i) (.head w) := by
                  have t := Derivable.var (R := S.R) (Γ := J) i
                  rw [eJ] at t
                  exact t
                exact Derivable.cumul typed (below cF cG)
  | const c =>
      intro J F G a b _ _ wb formedJ formedF _ long smallF _
      cases long with
      | neutralType ls htop le =>
          cases ls with
          | const role declared typed e =>
              exact spine_small_wide facts algebra wb.narrows_left formedJ formedF (.const role declared typed e)
                (.const role declared (typed_narrow wb.narrows_left typed) (typeEq_narrow wb.narrows_left e)) htop le
                smallF
  | head h =>
      intro J F G a b ha _ _ _ formedF _ _ smallF _
      obtain ⟨_, typing, c⟩ := head_typed_cumulative facts algebra formedF ha smallF
      exact Derivable.cumul (Derivable.headType typing) c
  | pi A B ihA ihB =>
      intro J F G a b ha hb wb formedJ formedF formedG long smallF smallG
      cases long with
      | pi lA lB _ =>
          have generationF : GenerationAt S.R F (.pi A B) (.head a) := Typed.generation smallF
          obtain ⟨u₁, u₂, w, tA, _, tB, _, join, le⟩ := generationF
          have cw : S.R.cumulative w a :=
            typeLe_head_cumulative facts algebra formedF (S.levels.join_level join).1 ha le
          obtain ⟨c₁, c₂⟩ := S.levels.join_upper join
          have generationG : GenerationAt S.R G (.pi A B) (.head b) := Typed.generation smallG
          obtain ⟨v₁, v₂, x, tAG, _, tBG, _, joinG, leG⟩ := generationG
          have cx : S.R.cumulative x b :=
            typeLe_head_cumulative facts algebra formedG (S.levels.join_level joinG).1 hb leG
          obtain ⟨d₁, d₂⟩ := S.levels.join_upper joinG
          have isA : IsType S.R J A := lA.isType
          have tA' := ihA ha hb wb formedJ formedF formedG lA (Derivable.cumul tA (algebra.trans c₁ cw))
            (Derivable.cumul tAG (algebra.trans d₁ cx))
          have tB' := ihB ha hb (wb.same A) (formedJ.snoc isA) (formedF.snoc (isType_narrow wb.narrows_left isA))
            (formedG.snoc (isType_narrow wb.narrows_right isA)) lB (Derivable.cumul tB (algebra.trans c₂ cw))
            (Derivable.cumul tBG (algebra.trans d₂ cx))
          obtain ⟨w', join'⟩ := S.levels.join_exists ha ha
          exact Derivable.cumul (Derivable.piForm tA' ha tB' ha join')
            (algebra.join_least join' (S.levels.cumulative_refl ha) (S.levels.cumulative_refl ha))
      | neutralType ls _ _ => cases ls
  | sigma A B ihA ihB =>
      intro J F G a b ha hb wb formedJ formedF formedG long smallF smallG
      cases long with
      | sigma lA lB _ =>
          have generationF : GenerationAt S.R F (.sigma A B) (.head a) := Typed.generation smallF
          obtain ⟨u₁, u₂, w, tA, _, tB, _, join, le⟩ := generationF
          have cw : S.R.cumulative w a :=
            typeLe_head_cumulative facts algebra formedF (S.levels.join_level join).1 ha le
          obtain ⟨c₁, c₂⟩ := S.levels.join_upper join
          have generationG : GenerationAt S.R G (.sigma A B) (.head b) := Typed.generation smallG
          obtain ⟨v₁, v₂, x, tAG, _, tBG, _, joinG, leG⟩ := generationG
          have cx : S.R.cumulative x b :=
            typeLe_head_cumulative facts algebra formedG (S.levels.join_level joinG).1 hb leG
          obtain ⟨d₁, d₂⟩ := S.levels.join_upper joinG
          have isA : IsType S.R J A := lA.isType
          have tA' := ihA ha hb wb formedJ formedF formedG lA (Derivable.cumul tA (algebra.trans c₁ cw))
            (Derivable.cumul tAG (algebra.trans d₁ cx))
          have tB' := ihB ha hb (wb.same A) (formedJ.snoc isA) (formedF.snoc (isType_narrow wb.narrows_left isA))
            (formedG.snoc (isType_narrow wb.narrows_right isA)) lB (Derivable.cumul tB (algebra.trans c₂ cw))
            (Derivable.cumul tBG (algebra.trans d₂ cx))
          obtain ⟨w', join'⟩ := S.levels.join_exists ha ha
          exact Derivable.cumul (Derivable.sigmaForm tA' ha tB' ha join')
            (algebra.join_least join' (S.levels.cumulative_refl ha) (S.levels.cumulative_refl ha))
      | neutralType ls _ _ => cases ls
  | id A s t ihA _ _ =>
      intro J F G a b ha hb wb formedJ formedF formedG long smallF smallG
      cases long with
      | id lA ls lt _ =>
          have generationF : GenerationAt S.R F (.id A s t) (.head a) := Typed.generation smallF
          obtain ⟨u₁, tA, hu₁, _, _, le⟩ := generationF
          have c : S.R.cumulative u₁ a := typeLe_head_cumulative facts algebra formedF hu₁ ha le
          have generationG : GenerationAt S.R G (.id A s t) (.head b) := Typed.generation smallG
          obtain ⟨v₁, tAG, hv₁, _, _, leG⟩ := generationG
          have d : S.R.cumulative v₁ b := typeLe_head_cumulative facts algebra formedG hv₁ hb leG
          exact Derivable.idForm (ihA ha hb wb formedJ formedF formedG lA (Derivable.cumul tA c)
            (Derivable.cumul tAG d)) ha ls.typed lt.typed
      | neutralType ls _ _ => cases ls
  | lam _ _ =>
      intro J F G a b _ _ _ _ _ _ long _ _
      cases long with
      | neutralType ls _ _ => cases ls
  | app f x _ _ =>
      intro J F G a b _ _ wb formedJ formedF _ long smallF _
      cases long with
      | neutralType ls htop le =>
          cases ls with
          | app lf eF lx eU =>
              rcases Long.narrow facts lf wb.narrows_left formedJ formedF with kept | ⟨_, _, e, _, _⟩
              · exact spine_small_wide facts algebra wb.narrows_left formedJ formedF (.app lf eF lx eU)
                  (.app kept (typeEq_narrow wb.narrows_left eF) (Long.term_narrow facts lx wb.narrows_left formedJ formedF)
                    (typeEq_narrow wb.narrows_left eU)) htop le smallF
              · exact absurd (TypeEq.trans S.levels eF.symm e) (TypeEq.pi_ne_head facts formedJ)
  | pair _ _ _ _ =>
      intro J F G a b _ _ _ _ _ _ long _ _
      cases long with
      | neutralType ls _ _ => cases ls
  | fst p _ =>
      intro J F G a b _ _ wb formedJ formedF _ long smallF _
      cases long with
      | neutralType ls htop le =>
          cases ls with
          | fst lp eP eU =>
              rcases Long.narrow facts lp wb.narrows_left formedJ formedF with kept | ⟨_, _, e, _, _⟩
              · exact spine_small_wide facts algebra wb.narrows_left formedJ formedF (.fst lp eP eU)
                  (.fst kept (typeEq_narrow wb.narrows_left eP) (typeEq_narrow wb.narrows_left eU)) htop le smallF
              · exact absurd (TypeEq.trans S.levels eP.symm e) (TypeEq.sigma_ne_head facts formedJ)
  | snd p _ =>
      intro J F G a b _ _ wb formedJ formedF _ long smallF _
      cases long with
      | neutralType ls htop le =>
          cases ls with
          | snd lp eP eU =>
              rcases Long.narrow facts lp wb.narrows_left formedJ formedF with kept | ⟨_, _, e, _, _⟩
              · exact spine_small_wide facts algebra wb.narrows_left formedJ formedF (.snd lp eP eU)
                  (.snd kept (typeEq_narrow wb.narrows_left eP) (typeEq_narrow wb.narrows_left eU)) htop le smallF
              · exact absurd (TypeEq.trans S.levels eP.symm e) (TypeEq.sigma_ne_head facts formedJ)
  | refl _ _ =>
      intro J F G a b _ _ _ _ _ _ long _ _
      cases long with
      | neutralType ls _ _ => cases ls

end Widening

/-! ## What the glb join forces -/

section Forcing

variable {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')

include facts roots heads algebra rigid complete headsTyped in
/-- **The glb join of two bodies**: a type of `U_cF` over `F` and a type of `U_cG` over `G`, equal over a common
narrowing, are equal to one type of `U_g` over the join, when the join widens each side toward its codomain. -/
theorem glb_join_body {n : Nat} {A F G J : Ctx Head n} {cF cG gl q : Head} (nF : CtxNarrows S.R F A)
    (nG : CtxNarrows S.R G A) (j : JoinOf S.R F G J) (wF : WidensBoth S.R cF cG J F G)
    (wG : WidensBoth S.R cG cF J G F) (formedA : CtxFormed S.R A) (formedF : CtxFormed S.R F)
    (formedG : CtxFormed S.R G) (formedJ : CtxFormed S.R J) {f g : Tm Head n} (hcF : S.R.isUniverse cF)
    (hcG : S.R.isUniverse cG) (hq : S.R.isUniverse q) (glb : IsGlb S.R gl cF cG) (cFq : S.R.cumulative cF q)
    (cGq : S.R.cumulative cG q) (tf : Typed S.R F f (.head cF)) (tg : Typed S.R G g (.head cG))
    (equal : Equal S.R A f g (.head q)) :
    ∃ Z, Typed S.R J Z (.head gl) ∧ Equal S.R F f Z (.head cF) ∧ Equal S.R G g Z (.head cG) := by
  obtain ⟨Zf, lZf, atZf⟩ := long_type_exists facts roots heads algebra rigid complete formedF ⟨cF, hcF, tf⟩
  obtain ⟨tZf, eZf⟩ := atZf hcF tf
  obtain ⟨Zg, lZg, atZg⟩ := long_type_exists facts roots heads algebra rigid complete formedG ⟨cG, hcG, tg⟩
  obtain ⟨tZg, eZg⟩ := atZg hcG tg
  have lZfA := Long.type_narrow facts lZf nF formedF formedA
  have lZgA := Long.type_narrow facts lZg nG formedG formedA
  have eA : TypeEq S.R A Zg Zf :=
    ⟨q, hq, (Derivable.cumulEq (equal_narrow nG eZg) cGq).symm.trans
      (equal.symm.trans (Derivable.cumulEq (equal_narrow nF eZf) cFq))⟩
  have same := long_type_unique facts roots heads algebra complete formedA lZgA lZfA eA
  have eG : Equal S.R G Zg Zf (.head cG) := Long.sameEqual facts heads lZg formedG same hcG tZg
  have tZfG : Typed S.R G Zf (.head cG) := (Equal.typed eG formedG).2
  -- The join, at the annotation's codomain.
  have tJ := typed_join facts roots heads algebra rigid complete headsTyped j formedF formedG formedJ
    (long_type_normal rigid lZf) (Derivable.cumul tZf cFq) (Derivable.cumul tZfG cGq) (IsType.head_of_universe hq)
  -- Its η-long form over the join, read back over each side.
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formedJ ⟨q, hq, tJ⟩
  obtain ⟨_, eZ⟩ := atZ hq tJ
  have lZF := Long.type_narrow facts lZ j.narrows_left formedJ formedF
  have lZG := Long.type_narrow facts lZ j.narrows_right formedJ formedG
  have eZF : Equal S.R F Zf Z (.head q) := equal_narrow j.narrows_left eZ
  have eZG : Equal S.R G Zf Z (.head q) := equal_narrow j.narrows_right eZ
  have tZF : Typed S.R F Z (.head cF) :=
    normal_typed_of_equal facts roots heads algebra rigid complete formedF hcF tZf ⟨q, hq, eZF⟩ lZF
  have tZG : Typed S.R G Z (.head cG) :=
    normal_typed_of_equal facts roots heads algebra rigid complete formedG hcG tZfG ⟨q, hq, eZG⟩ lZG
  -- The joint widening toward each codomain, then the least universe.
  have zF : Typed S.R J Z (.head cF) :=
    typed_widen_both facts algebra Z hcF hcG wF formedJ formedF formedG lZ tZF tZG
  have zG : Typed S.R J Z (.head cG) :=
    typed_widen_both facts algebra Z hcG hcF wG formedJ formedG formedF lZ tZG tZF
  obtain ⟨ℓ, hℓ, tℓ, least⟩ := least_universe facts algebra headsTyped Z formedJ lZ
  have tZJ : Typed S.R J Z (.head gl) := Derivable.cumul tℓ (glb.2.2.2 ℓ hℓ (least cF hcF zF) (least cG hcG zG))
  have eZF' : Equal S.R F Zf Z (.head cF) :=
    universe_injective facts roots heads algebra rigid complete formedF hcF hq tZf tZF eZF
  have eZG' : Equal S.R G Zf Z (.head cG) :=
    universe_injective facts roots heads algebra rigid complete formedG hcG hq tZfG tZG eZG
  exact ⟨Z, tZJ, eZf.trans eZF', eZg.trans (eG.trans eZG')⟩

include facts roots heads algebra rigid complete headsTyped in
/-- **What the glb join forces, under the binders.** -/
theorem glbJoinK_open : ∀ {ps psF : List Head}, List.Forall₂ S.R.cumulative ps psF →
    ∀ {psG : List Head}, List.Forall₂ S.R.cumulative ps psG → ∀ {psJ : List Head}, JoinsK S.R psF psG psJ →
    ∀ {cF cG : Head}, List.Forall₂ (CrossAt S.R cF cG) psF psG →
    ∀ {n : Nat} {A F G J : Ctx Head n}, CtxNarrows S.R F A → CtxNarrows S.R G A → JoinOf S.R F G J →
      WidensBoth S.R cF cG J F G → WidensBoth S.R cG cF J G F → CtxFormed S.R A → CtxFormed S.R F →
      CtxFormed S.R G → CtxFormed S.R J →
      ∀ {f g : Tm Head n} {gl q : Head}, AllUniverses S.R ps → AllUniverses S.R psF → AllUniverses S.R psG →
      S.R.isUniverse cF → S.R.isUniverse cG → S.R.isUniverse q → IsGlb S.R gl cF cG → S.R.cumulative cF q →
      S.R.cumulative cG q → Typed S.R F f (famCode psF cF) → Typed S.R G g (famCode psG cG) →
      Equal S.R A (etaExp ps.length f) (etaExp ps.length g) (famCode ps q) →
      ∃ h, Typed S.R J h (famCode psJ gl) ∧ Equal S.R F f (etaExp psF.length h) (famCode psF cF) ∧
        Equal S.R G g (etaExp psG.length h) (famCode psG cG) := by
  intro ps psF annF
  induction annF with
  | nil =>
      intro psG annG psJ joins cF cG _ n A F G J nF nG j wF wG formedA formedF formedG formedJ f g gl q _ _ _ hcF
        hcG hq glb cFq cGq tf tg equal
      cases annG
      cases joins
      exact glb_join_body facts roots heads algebra rigid complete headsTyped nF nG j wF wG formedA formedF formedG
        formedJ hcF hcG hq glb cFq cGq tf tg equal
  | @cons p pF ps' psF' belowF restF ih =>
      intro psG annG psJ joins cF cG cross n A F G J nF nG j wF wG formedA formedF formedG formedJ f g gl q univ
        univF univG hcF hcG hq glb cFq cGq tf tg equal
      cases annG with
      | @cons _ pG _ psG' belowG restG =>
          cases joins with
          | @cons _ _ pJ _ _ psJ' hpJ lub restJ =>
              cases cross with
              | cons here restC =>
                  have hp := univ.head
                  have hpF := univF.head
                  have hpG := univG.head
                  have univJ : AllUniverses S.R (pJ :: psJ') := JoinsK.universes (.cons hpJ lub restJ)
                  have formedA' : CtxFormed S.R (.snoc A (.head p)) := formedA.snoc (IsType.head_of_universe hp)
                  have formedF' : CtxFormed S.R (.snoc F (.head pF)) := formedF.snoc (IsType.head_of_universe hpF)
                  have formedG' : CtxFormed S.R (.snoc G (.head pG)) := formedG.snoc (IsType.head_of_universe hpG)
                  have formedJ' : CtxFormed S.R (.snoc J (.head pJ)) := formedJ.snoc (IsType.head_of_universe hpJ)
                  -- The widened binder lies below each codomain as soon as both declarations lie below theirs.
                  have toF : S.R.cumulative pF cF → S.R.cumulative pG cG → S.R.cumulative pJ cF :=
                    fun hF hG => lub.2.2 cF hcF hF (here hF hG).2
                  have toG : S.R.cumulative pG cG → S.R.cumulative pF cF → S.R.cumulative pJ cG :=
                    fun hG hF => lub.2.2 cG hcG (here hF hG).1 hG
                  change Equal S.R A (.lam (etaExp ps'.length (.app (Presentation.rename wk f) (.var 0))))
                    (.lam (etaExp ps'.length (.app (Presentation.rename wk g) (.var 0))))
                    (.pi (.head p) (famCode ps' q)) at equal
                  -- Open the equation at `x : U_p` over the annotation's telescope.
                  have opened := equal_of_lam_left facts formedA equal
                  have tgA : Typed S.R A g (famCode (pG :: psG') cG) := typed_narrow nG tg
                  have gBody := raisedK_typed restG univ.tail hq cGq formedA' (openK_typed tgA belowG)
                  obtain ⟨uP, huP, tPiP⟩ := famCode_isType (p :: ps') univ hq formedA
                  have tPiP' : Typed S.R A (.pi (.head p) (famCode ps' q)) (.head uP) := tPiP
                  have narrowEq := opened.trans (beta_open tPiP' huP gBody)
                  -- The induction, over the four telescopes extended by their binders.
                  obtain ⟨h', th', eF', eG'⟩ := ih restG restJ restC (.lower nF belowF) (.lower nG belowG)
                    (.join j hpF hpG hpJ lub) (.lower wF hpJ hpF hpG lub.1 lub.2.1 toF)
                    (.lower wG hpJ hpG hpF lub.2.1 lub.1 toG) formedA' formedF' formedG' formedJ' univ.tail
                    univF.tail univG.tail hcF hcG hq glb cFq cGq (openK_typed tf (S.levels.cumulative_refl hpF))
                    (openK_typed tg (S.levels.cumulative_refl hpG)) narrowEq
                  -- The family `λ x. h'`, at the greatest lower bound.
                  obtain ⟨uJ, huJ, tPiJ⟩ := famCode_isType (pJ :: psJ') univJ glb.1 formedJ
                  have tPiJ' : Typed S.R J (.pi (.head pJ) (famCode psJ' gl)) (.head uJ) := tPiJ
                  have th : Typed S.R J (.lam h') (famCode (pJ :: psJ') gl) := Derivable.lamIntro tPiJ' huJ th'
                  refine ⟨.lam h', th, ?_, ?_⟩
                  · exact eta_join_side facts j.narrows_left formedF lub.1 restJ.left univF univJ hcF glb.1 glb.2.1
                      tf th eF'
                  · exact eta_join_side facts j.narrows_right formedG lub.2.1 restJ.right univG univJ hcG glb.1
                      glb.2.2.1 tg th eG'

include facts roots heads algebra rigid complete headsTyped in
/-- **What the glb join forces at a flex–flex equation**: under the condition, every solution sends both unknowns to
η-expansions of one family of `Π (x̄ : U_{p̄J}). U_g`. -/
theorem glbJoinK_forces {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) {gl : Head}
    (glb : IsGlb S.R gl v.cl v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ)
    (cross : List.Forall₂ (CrossAt S.R v.cl v.cr) v.psl v.psr) : JoinForces v psJ gl := by
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
  exact glbJoinK_open facts roots heads algebra rigid complete headsTyped v.domain_left v.domain_right joins cross
    (CtxNarrows.refl Δ.raw) (CtxNarrows.refl Δ.raw) (JoinOf.refl S.R Δ.raw) (WidensBoth.refl v.cl v.cr Δ.raw)
    (WidensBoth.refl v.cr v.cl Δ.raw) Δ.formed Δ.formed Δ.formed Δ.formed v.universes v.universes_left
    v.universes_right v.universe_cl v.universe_cr v.universe_q glb v.codomain_left v.codomain_right tF tG equal

include facts roots heads algebra rigid complete headsTyped in
/-- **The glb join is exact**: `G` declared again at `Π (x̄ : U_{p̄J}). U_g`, both unknowns sent to its
η-expansion. -/
theorem glbJoinK_exact {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {gl : Head} (glb : IsGlb S.R gl v.cl v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ)
    (cross : List.Forall₂ (CrossAt S.R v.cl v.cr) v.psl v.psr) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (joinMKHom Θ families v joins glb.1 glb.2.1 glb.2.2.1)
      ((frames S.levels).applyStore (joinMKHom Θ families v joins glb.1 glb.2.1 glb.2.2.1) rest) :=
  joinMK_exact families v joins glb.1 glb.2.1 glb.2.2.1
    (glbJoinK_forces facts roots heads algebra rigid complete headsTyped v glb joins cross) rest

include facts roots heads algebra rigid complete headsTyped in
/-- **The glb join on a whole store**, the other equations' sides of `F` and `G` re-read; exact. -/
theorem glbJoinRereadK_exact [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
    [DecidableRel S.R.cumulative] {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)}
    (v : FlexK e) {gl : Head} (glb : IsGlb S.R gl v.cl v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ)
    (cross : List.Forall₂ (CrossAt S.R v.cl v.cr) v.psl v.psr) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (joinMKHom Θ families v joins glb.1 glb.2.1 glb.2.2.1)
      (joinStore families v joins glb.1 glb.2.1 glb.2.2.1 rest) :=
  joinRereadK_exact families v joins glb.1 glb.2.1 glb.2.2.1
    (glbJoinK_forces facts roots heads algebra rigid complete headsTyped v glb joins cross) rest

end Forcing

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
