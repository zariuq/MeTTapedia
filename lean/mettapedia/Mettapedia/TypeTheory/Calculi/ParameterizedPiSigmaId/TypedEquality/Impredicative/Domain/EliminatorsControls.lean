import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Eliminators
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ProjectionLawsControls

/-!
# Controls for the eliminators as constants that carry their types

The reading of the controls interprets every head as the universe and `num` as the
numbers (`EliminatorControls.rd`).

**Positive, at closed arguments.**

* `J num 0 (λ y p. num) 0 0 (refl 0)` denotes `0` (`j_closed`).
* `num-rec (λ _. num) 0 (λ v r. suc r)` sends `0` to `0` and `suc 0` to `1`
  (`numRec_closed_zero`, `numRec_closed_succ`).

**The identity type of the domain does not supply endpoint equations.** `refl ⊥` is
an element of every identity type (`refl_bot_mem`), `Id num 0 1` included. So the
spine facts hold at `J num 0 (λ y p. num) 0 1 (refl ⊥)`, whose endpoints differ, and
the linear rule gives the method there (`j_distinct_endpoints`).

**Negative: an ill-typed spine.** `J num 0 (λ y p. num) 0 1 (refl 0)` does not have
spine facts: `refl 0` is not an element of `Id num 0 1` (`ill_typed_spine`).

**The linear rule does not see the projections.** The eliminator's function without
any projection (`jRaw_linear`) and the eliminator without the argument projections
(`jCod_linear`) satisfy the linear rule too. What the projections are needed for is
that the constant is an element of its declared type:

* without the codomain projection it is not, already at typed arguments: at
  `J num 0 (λ y p. Id num y y) (refl 0) 1 (refl ⊥)`, whose arguments have spine facts,
  it returns `refl 0`, which is not an element of `Id num 1 1` (`jRaw_not_typed`);
* without the argument projections it is not either, at `J U num (λ y p. y) U U
  (refl ⊥)`: the method `U` is not an element of `P num (refl num) = num`, and the
  projected constant drops it (`jCod_not_typed`).

**Negative: both hypotheses of the linear rule are needed.**

* The contractum's typing: at `J num 0 (λ y p. Id num y y) (refl 0) 1 (refl ⊥)` the
  spine facts hold, the method `refl 0` is not an element of the instantiated type
  `Id num 1 1`, and the spine does not denote the method (`right_premise_needed`).
* The spine facts about the arguments: at
  `J num 0 (λ y p. Id num y y) (refl 1) 1 (refl ⊥)` the instantiated type is
  `Id num 1 1` and the method `refl 1` is an element of it, but not of its parameter
  type `Id num 0 0`, and the spine does not denote the method
  (`argument_facts_needed`).

**Negative: the decoding of an equation code needs the contractum's typing.** At
`holds (eq@num U U)` the contractum `Id num U U` is not a type, and the decoding
differs from it (`decode_eq_needs_right`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain
namespace EliminatorControls

open Annotated (CTm)
open Ideal

/-! ## The reading and some elements -/

/-- The reading of the controls: every head is the universe, `num` the numbers, and
every other constant the least element. -/
def rd : Reading Unit where
  head _ := Elem.univ
  const c := if c = `num then natI else bot

/-- The names of numeral recursion. -/
def nm : NumNames Unit := ⟨(), `num, `zero, `suc⟩

theorem rd_num : rd.const nm.num = natI := by
  show (if (`num : DeclName) = `num then natI else bot) = natI
  exact if_pos rfl

/-- One. -/
def oneI : Ideal := succI zeroI

theorem natI_type : projT univIdeal natI = natI :=
  projT_principal_eq (a := Elem.univ) (fun _ h => ent_of_mem h) Elem.ty_univ_univ nat_type

theorem univ_type : projT univIdeal univIdeal = univIdeal :=
  projT_principal_eq (a := Elem.univ) (fun _ h => ent_of_mem h) Elem.ty_univ_univ
    Elem.ty_univ_univ

theorem oneI_type : projT natI oneI = oneI := projT_natI_succI projT_natI_zeroI

theorem oneI_not_mem_zero : ¬ oneI.Mem (.tag .zero) := succI_not_mem_tag (by decide) zeroI

theorem refl_principal (w : List Tok) : Ideal.refl (principal w) = principal (Elem.refl w) := by
  apply le_antisymm
  · refine closure_le fun t ht => ?_
    rcases ht with rfl | ⟨s, rfl, hs⟩
    · exact ent_of_mem List.mem_cons_self
    · show ent (Elem.refl w) (.arg .refl 0 [] s) = true
      rw [ent_arg, List.all_nil, Bool.true_and, Elem.refl, args_cons_tag, args_map_arg_same]
      exact hs
  · intro t ht
    refine (Ideal.refl (principal w)).closed (v := Elem.refl w) (fun s hs => ?_) ht
    rcases List.mem_cons.1 hs with rfl | hs
    · exact subset_closure (.inl rfl)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
      exact subset_closure (.inr ⟨r, rfl, ent_of_mem hr⟩)

theorem succI_principal (w : List Tok) : succI (principal w) = principal (Elem.succ w) := by
  apply le_antisymm
  · refine closure_le fun t ht => ?_
    rcases ht with rfl | ⟨s, rfl, hs⟩
    · exact ent_of_mem List.mem_cons_self
    · show ent (Elem.succ w) (.arg .succ 0 [] s) = true
      rw [ent_arg, List.all_nil, Bool.true_and, Elem.succ, args_cons_tag, args_map_arg_same]
      exact hs
  · intro t ht
    refine (succI (principal w)).closed (v := Elem.succ w) (fun s hs => ?_) ht
    rcases List.mem_cons.1 hs with rfl | hs
    · exact subset_closure (.inl rfl)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
      exact subset_closure (.inr ⟨r, rfl, ent_of_mem hr⟩)

theorem oneI_eq : oneI = principal (Elem.succ Elem.zero) := succI_principal Elem.zero

theorem one_nat : Ty (Elem.succ Elem.zero) Elem.nat :=
  (Elem.ty_succ List.mem_cons_self).2 (Elem.ty_zero List.mem_cons_self)

/-! ## Identity types and reflexivity -/

/-- The endpoint component of a token of an identity type is in its endpoint. -/
theorem mem_ident_endpoint {A I J : Ideal} {C : List Tok} {s : Tok}
    (h : (Ideal.ident A I J).Mem (.arg .ident 2 C s)) : J.Mem s := by
  obtain ⟨w, hw, h⟩ := h
  rw [ent_arg, Bool.and_eq_true] at h
  refine J.closed (v := args .ident 2 w) (fun c hc => ?_) h.2
  rcases mem_args_iff.1 hc with ⟨C', hC'⟩ | ⟨h2, -⟩
  · rcases hw _ hC' with h' | ⟨d, h', -⟩ | ⟨C'', s', h', -, -⟩ | ⟨C'', s', h', -, hs'⟩
    · cases h'
    · simp at h'
    · simp at h'
    · simp only [Tok.arg.injEq, true_and] at h'
      obtain ⟨-, rfl⟩ := h'
      exact hs'
  · simp at h2

/-- **A reflexivity whose point has a tag its second endpoint lacks is not typed at
the identity type**: whatever the element, its projection onto the identity type
has no such reflexivity token. -/
theorem reflTag_not_mem {A I J R : Ideal} {k : Kind} (hJ : ¬ J.Mem (.tag k)) :
    ¬ (projT (Ideal.ident A I J) R).Mem (.arg .refl 0 [] (.tag k)) := by
  rintro ⟨v, hv, hent⟩
  rw [ent_arg, List.all_nil, Bool.true_and, ent_tag, hasTag_iff] at hent
  rcases mem_args_iff.1 hent with ⟨C, hC⟩ | ⟨-, t, ht, hk, hd⟩
  · obtain ⟨-, a, ha, -, hat⟩ := hv _ hC
    obtain ⟨-, -, -, -, h2⟩ := tyTok_reflPoint.1 hat
    rw [ent_tag, hasTag_iff] at h2
    rcases mem_args_iff.1 h2 with ⟨C', hC'⟩ | ⟨h, -⟩
    · exact hJ (mem_ident_endpoint (ha _ hC'))
    · simp at h
  · obtain ⟨-, a, -, -, hat⟩ := hv t ht
    cases t with
    | tag => cases hd
    | arg k' i C s =>
        change k' = .refl at hk
        subst hk
        change Tok.tag k ∈ C at hd
        rcases Decidable.em ((Kind.refl, i) ∈ argSlots) with hs | hother
        · have hi : i = 0 := by simpa [argSlots] using hs
          subst hi
          obtain ⟨-, rfl, -⟩ := tyTok_reflPoint.1 hat
          cases hd
        · exact tyTok_arg_other hother hat
    | fn k' C X Y =>
        change k' = .refl at hk
        subst hk
        exact tyTok_fn_other (by decide) hat

theorem mem_refl_arg {I : Ideal} {s : Tok} (h : I.Mem s) :
    (Ideal.refl I).Mem (.arg .refl 0 [] s) :=
  subset_closure (.inr ⟨s, rfl, h⟩)

theorem refl_bot_eq : Ideal.refl bot = principal [.tag .refl] := refl_principal []

/-- **`refl ⊥` is an element of every identity type.** -/
theorem refl_bot_mem (A I J : Ideal) : projT (Ideal.ident A I J) (Ideal.refl bot) = Ideal.refl bot := by
  rw [refl_bot_eq]
  refine projT_principal_eq (a := [.tag .ident]) (fun t ht => ?_)
    (Elem.ty_tag (k := .ident) trivial Elem.isUniv_univ) (fun t ht => ?_)
  · rw [List.mem_singleton.1 ht]
    exact subset_closure (.inl rfl)
  · rw [List.mem_singleton.1 ht]
    exact tyTok_tag_refl.2 List.mem_cons_self

theorem below_elem_ident (c u v : List Tok) :
    Ideal.Below (Elem.ident c u v) (Ideal.ident (principal c) (principal u) (principal v)) := by
  intro t ht
  simp only [Elem.ident, List.mem_cons, List.mem_append, List.mem_map] at ht
  rcases ht with rfl | (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩
  · exact subset_closure (.inl rfl)
  · exact subset_closure (.inr (.inl ⟨s, rfl, ent_of_mem hs⟩))
  · exact subset_closure (.inr (.inr (.inl ⟨c, s, rfl, fun d hd => ent_of_mem hd, ent_of_mem hs⟩)))
  · exact subset_closure (.inr (.inr (.inr ⟨c, s, rfl, fun d hd => ent_of_mem hd, ent_of_mem hs⟩)))

theorem ty_refl_self {c u : List Tok} (hu : Ty u c) : Ty (Elem.refl u) (Elem.ident c u u) := by
  rw [Elem.ty_refl (a := Elem.ident c u u) List.mem_cons_self]
  refine ⟨hu.mono (Le.of_subset fun d hd => mem_args_of_arg (C := [])
      (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map_of_mem hd))))),
    Le.of_subset fun s hs => mem_args_of_arg (C := c)
      (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map_of_mem hs)))),
    Le.of_subset fun s hs => mem_args_of_arg (C := c)
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem hs)))⟩

/-- A reflexivity at a typed point is an element of the identity type between the
point and itself. -/
theorem refl_mem_self {c u : List Tok} (hc : Ty c Elem.univ) (hu : Ty u c) :
    projT (Ideal.ident (principal c) (principal u) (principal u)) (Ideal.refl (principal u)) =
      Ideal.refl (principal u) := by
  rw [refl_principal]
  exact projT_principal_eq (below_elem_ident c u u) (Elem.ty_ident Elem.isUniv_univ hc hu hu)
    (ty_refl_self hu)

theorem refl_zero_mem : projT (Ideal.ident natI zeroI zeroI) (Ideal.refl zeroI) = Ideal.refl zeroI :=
  refl_mem_self nat_type (Elem.ty_zero List.mem_cons_self)

theorem refl_one_mem : projT (Ideal.ident natI oneI oneI) (Ideal.refl oneI) = Ideal.refl oneI := by
  rw [oneI_eq]
  exact refl_mem_self nat_type one_nat

/-! ## The motives -/

/-- The type of the eliminator's motive over `A` and `x`: `Π (y : A). Id A x y → U`. -/
abbrev motiveTypeC : CTm Unit 2 := .pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) (.head ()))

theorem app_app_motive (α ξ f y p : Ideal) :
    app (app (projT (cinterp rd motiveTypeC (Env.cons ξ (Env.cons α Env.nil))) f) y) p =
      projT univIdeal (app (app f (projT α y)) (projT (Ideal.ident α ξ (projT α y)) p)) := by
  rw [app_projT_cinterp_pi, app_projT_cinterp_pi]
  rfl

/-- The motive `λ y p. num`. -/
def natMotive : Ideal :=
  projT (cinterp rd motiveTypeC (Env.cons zeroI (Env.cons natI Env.nil))) (lam fun _ => lam fun _ => natI)

theorem app_app_natMotive (y p : Ideal) : app (app natMotive y) p = natI := by
  rw [natMotive, app_app_motive, app_lam_const, app_lam_const, natI_type]

theorem cont_ident_diag (A : Ideal) : Cont fun z => Ideal.ident A z z :=
  Cont.of_closure (P := fun z t => t = .tag .ident ∨ (∃ d, t = .arg .ident 0 [] d ∧ A.Mem d) ∨
      (∃ C s, t = .arg .ident 1 C s ∧ Ideal.Below C A ∧ z.Mem s) ∨
      ∃ C s, t = .arg .ident 2 C s ∧ Ideal.Below C A ∧ z.Mem s)
    (fun h _ ht => ht.imp_right (Or.imp_right (Or.imp (fun ⟨C, s, e, hC, hs⟩ => ⟨C, s, e, hC, h s hs⟩)
      fun ⟨C, s, e, hC, hs⟩ => ⟨C, s, e, hC, h s hs⟩)))
    fun {_ _} ht => by
      rcases ht with rfl | ⟨d, rfl, hd⟩ | ⟨C, s, rfl, hC, hs⟩ | ⟨C, s, rfl, hC, hs⟩
      · exact ⟨[], fun _ h => absurd h List.not_mem_nil, .inl rfl⟩
      · exact ⟨[], fun _ h => absurd h List.not_mem_nil, .inr (.inl ⟨d, rfl, hd⟩)⟩
      · exact ⟨[s], fun r hr => by rw [List.mem_singleton.1 hr]; exact hs,
          .inr (.inr (.inl ⟨C, s, rfl, hC, ent_of_mem List.mem_cons_self⟩))⟩
      · exact ⟨[s], fun r hr => by rw [List.mem_singleton.1 hr]; exact hs,
          .inr (.inr (.inr ⟨C, s, rfl, hC, ent_of_mem List.mem_cons_self⟩))⟩

/-- The motive `λ y p. Id num y y`. -/
def idMotive : Ideal :=
  projT (cinterp rd motiveTypeC (Env.cons zeroI (Env.cons natI Env.nil)))
    (lam fun Y => lam fun _ => Ideal.ident natI (principal Y) (principal Y))

theorem app_app_idMotive (y p : Ideal) :
    app (app idMotive y) p = Ideal.ident natI (projT natI y) (projT natI y) := by
  have hH : Cont fun z => lam fun _ => Ideal.ident natI z z :=
    cont_lam_param fun _ => cont_ident_diag natI
  have e : app (lam fun Y => lam fun _ => Ideal.ident natI (principal Y) (principal Y)) (projT natI y) =
      lam fun _ => Ideal.ident natI (projT natI y) (projT natI y) :=
    app_lam_principal hH _
  rw [idMotive, app_app_motive, e, app_lam_const]
  exact projT_univ_eq_self_iff.2 (typeGenerated_ident (typeGenerated_principal nat_type)
    (projT_projT _ _) (projT_projT _ _))

/-! ## Positive: the linear rule at closed arguments -/

/-- The spine facts at `J num 0 (λ y p. num) 0 y p`. -/
theorem natMotive_spine {η p : Ideal} (hη : projT natI η = η)
    (hp : projT (Ideal.ident natI zeroI η) p = p) :
    SpineTyped (jTypeI rd ()) [natI, zeroI, natMotive, zeroI, η, p] :=
  (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨natI_type,
    (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨projT_natI_zeroI,
      (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨projT_projT _ _,
        (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨by
            show projT (app (app natMotive zeroI) (Ideal.refl zeroI)) zeroI = zeroI
            rw [app_app_natMotive, projT_natI_zeroI],
          (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨hη,
            (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨hp, trivial⟩⟩⟩⟩⟩⟩

/-- **Positive**: `J num 0 (λ y p. num) 0 0 (refl 0)` denotes `0`. -/
theorem j_closed :
    appSpine (jConst rd ()) [natI, zeroI, natMotive, zeroI, zeroI, Ideal.refl zeroI] = zeroI := by
  have spine := natMotive_spine projT_natI_zeroI refl_zero_mem
  refine jConst_linear rd () ⟨rfl, spine⟩ ?_
  rw [instPi_jType spine, app_app_natMotive, projT_natI_zeroI]

/-! ## The identity type does not supply endpoint equations -/

/-- **`refl ⊥` is an element of `Id num 0 1`**, whose endpoints differ. -/
theorem refl_bot_zero_one :
    projT (Ideal.ident natI zeroI oneI) (Ideal.refl bot) = Ideal.refl bot :=
  refl_bot_mem _ _ _

/-- **The spine facts hold at `J num 0 (λ y p. num) 0 1 (refl ⊥)`**, and the linear rule
gives the method there, although the endpoints `0` and `1` differ. -/
theorem j_distinct_endpoints :
    SpineTyped (jTypeI rd ()) [natI, zeroI, natMotive, zeroI, oneI, Ideal.refl bot] ∧
      appSpine (jConst rd ()) [natI, zeroI, natMotive, zeroI, oneI, Ideal.refl bot] = zeroI := by
  have spine := natMotive_spine oneI_type refl_bot_zero_one
  refine ⟨spine, jConst_linear rd () ⟨rfl, spine⟩ ?_⟩
  rw [instPi_jType spine, app_app_natMotive, projT_natI_zeroI]

/-! ## Negative: an ill-typed spine -/

/-- **An ill-typed spine has no spine facts**: at `J num 0 (λ y p. num) 0 1 (refl 0)`,
`refl 0` is not an element of `Id num 0 1`. -/
theorem ill_typed_spine :
    ¬ SpineTyped (jTypeI rd ()) [natI, zeroI, natMotive, zeroI, oneI, Ideal.refl zeroI] := by
  intro spine
  obtain ⟨-, s1⟩ := (spineTyped_cinterp_pi rd _ _ _ _ _).1 spine
  obtain ⟨-, s2⟩ := (spineTyped_cinterp_pi rd _ _ _ _ _).1 s1
  obtain ⟨-, s3⟩ := (spineTyped_cinterp_pi rd _ _ _ _ _).1 s2
  obtain ⟨-, s4⟩ := (spineTyped_cinterp_pi rd _ _ _ _ _).1 s3
  obtain ⟨-, s5⟩ := (spineTyped_cinterp_pi rd _ _ _ _ _).1 s4
  obtain ⟨h6, -⟩ := (spineTyped_cinterp_pi rd _ _ _ _ _).1 s5
  have h6' : projT (Ideal.ident natI zeroI oneI) (Ideal.refl zeroI) = Ideal.refl zeroI := h6
  have hmem := mem_refl_arg (I := zeroI) zeroI_mem_zero
  rw [← h6'] at hmem
  exact reflTag_not_mem oneI_not_mem_zero hmem

/-! ## The linear rule does not see the projections -/

/-- **The eliminator's function without projections satisfies the linear rule**, with
no hypothesis. -/
theorem jRaw_linear (α ξ π δ η a : Ideal) :
    appSpine jRaw [α, ξ, π, δ, η, Ideal.refl a] = δ := by
  rw [appSpine_jRaw, whenTag_of_mem (refl_mem_tag a)]

/-- The eliminator's function with the codomain projection and without the argument
projections. -/
def jCod : Ideal :=
  lam fun _ => lam fun _ => lam fun P => lam fun D => lam fun Y => lam fun Q =>
    projT (app (app (principal P) (principal Y)) (principal Q))
      (whenTag .refl (principal Q) (principal D))

theorem appSpine_jCod (α ξ π δ η p : Ideal) :
    appSpine jCod [α, ξ, π, δ, η, p] = projT (app (app π η) p) (whenTag .refl p δ) := by
  have h₃ : Cont fun π' => lam fun D => lam fun Y => lam fun Q =>
      projT (app (app π' (principal Y)) (principal Q)) (whenTag .refl (principal Q) (principal D)) :=
    cont_lam_param fun _ => cont_lam_param fun Y => cont_lam_param fun Q =>
      (cont_projT_type _).comp ((cont₂_app.left (principal Q)).comp (cont₂_app.left (principal Y)))
  have h₄ : Cont fun d => lam fun Y => lam fun Q =>
      projT (app (app π (principal Y)) (principal Q)) (whenTag .refl (principal Q) d) :=
    cont_lam_param fun Y => cont_lam_param fun Q =>
      (cont_projT _).comp ((cont₂_whenTag .refl).right (principal Q))
  have h₅ : Cont fun y => lam fun Q => projT (app (app π y) (principal Q)) (whenTag .refl (principal Q) δ) :=
    cont_lam_param fun Q =>
      (cont_projT_type _).comp ((cont₂_app.left (principal Q)).comp (cont₂_app.right π))
  have h₆ : Cont fun q => projT (app (app π η) q) (whenTag .refl q δ) :=
    cont₂_projT.comp (cont₂_app.right (app π η)) ((cont₂_whenTag .refl).left δ)
  have e₃ : app (lam fun P => lam fun D => lam fun Y => lam fun Q =>
      projT (app (app (principal P) (principal Y)) (principal Q))
        (whenTag .refl (principal Q) (principal D))) π =
      lam fun D => lam fun Y => lam fun Q =>
        projT (app (app π (principal Y)) (principal Q)) (whenTag .refl (principal Q) (principal D)) :=
    app_lam_principal h₃ π
  have e₄ : app (lam fun D => lam fun Y => lam fun Q =>
      projT (app (app π (principal Y)) (principal Q)) (whenTag .refl (principal Q) (principal D))) δ =
      lam fun Y => lam fun Q => projT (app (app π (principal Y)) (principal Q)) (whenTag .refl (principal Q) δ) :=
    app_lam_principal h₄ δ
  have e₅ : app (lam fun Y => lam fun Q =>
      projT (app (app π (principal Y)) (principal Q)) (whenTag .refl (principal Q) δ)) η =
      lam fun Q => projT (app (app π η) (principal Q)) (whenTag .refl (principal Q) δ) :=
    app_lam_principal h₅ η
  have e₆ : app (lam fun Q => projT (app (app π η) (principal Q)) (whenTag .refl (principal Q) δ)) p =
      projT (app (app π η) p) (whenTag .refl p δ) :=
    app_lam_principal h₆ p
  show app (app (app (app (app (app jCod α) ξ) π) δ) η) p = _
  unfold jCod
  rw [app_lam_const, app_lam_const, e₃, e₄, e₅, e₆]

/-- **The eliminator without the argument projections satisfies the linear rule** at
every spine with spine facts whose method is an element of the instantiated type. -/
theorem jCod_linear {α ξ π δ η a τ : Ideal}
    (facts : SpineFacts (jTypeI rd ()) [α, ξ, π, δ, η, Ideal.refl a] τ) (right : projT τ δ = δ) :
    appSpine jCod [α, ξ, π, δ, η, Ideal.refl a] = δ := by
  obtain ⟨hτ, spine⟩ := facts
  rw [appSpine_jCod, whenTag_of_mem (refl_mem_tag a), ← instPi_jType spine, hτ, right]

/-! ## Negative: the codomain projection -/

/-- The spine facts at `J num 0 (λ y p. Id num y y) (refl 0) 1 (refl ⊥)`. -/
theorem idMotive_spine :
    SpineTyped (jTypeI rd ()) [natI, zeroI, idMotive, Ideal.refl zeroI, oneI, Ideal.refl bot] :=
  (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨natI_type,
    (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨projT_natI_zeroI,
      (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨projT_projT _ _,
        (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨by
            show projT (app (app idMotive zeroI) (Ideal.refl zeroI)) (Ideal.refl zeroI) =
              Ideal.refl zeroI
            rw [app_app_idMotive, projT_natI_zeroI]
            exact refl_zero_mem,
          (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨oneI_type,
            (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨refl_bot_mem _ _ _, trivial⟩⟩⟩⟩⟩⟩

/-- **Without the codomain projection, the eliminator is not an element of its
declared type.** At `J num 0 (λ y p. Id num y y) (refl 0) 1 (refl ⊥)`, whose arguments
have spine facts, the function returns `refl 0`, which is not an element of the
instantiated type `Id num 1 1`. -/
theorem jRaw_not_typed : projT (jTypeI rd ()) jRaw ≠ jRaw := by
  intro h
  have e := appSpine_churchConst jRaw (churchTele_cinterp rd (jTypeC ()) Env.nil) (Nat.le_refl _)
    idMotive_spine
  rw [h, instPi_jType idMotive_spine, app_app_idMotive, oneI_type, appSpine_jRaw,
    whenTag_of_mem (refl_mem_tag bot)] at e
  have hmem := mem_refl_arg (I := zeroI) zeroI_mem_zero
  rw [e] at hmem
  exact reflTag_not_mem oneI_not_mem_zero hmem

/-- **The linear rule needs the contractum's typing.** At
`J num 0 (λ y p. Id num y y) (refl 0) 1 (refl ⊥)` the spine facts hold, but the
method `refl 0` is not an element of the instantiated type `Id num 1 1`, and the
spine does not denote the method. -/
theorem right_premise_needed :
    SpineTyped (jTypeI rd ()) [natI, zeroI, idMotive, Ideal.refl zeroI, oneI, Ideal.refl bot] ∧
      projT (Ideal.ident natI oneI oneI) (Ideal.refl zeroI) ≠ Ideal.refl zeroI ∧
      appSpine (jConst rd ()) [natI, zeroI, idMotive, Ideal.refl zeroI, oneI, Ideal.refl bot] ≠
        Ideal.refl zeroI := by
  have hne : projT (Ideal.ident natI oneI oneI) (Ideal.refl zeroI) ≠ Ideal.refl zeroI := by
    intro h
    have hmem := mem_refl_arg (I := zeroI) zeroI_mem_zero
    rw [← h] at hmem
    exact reflTag_not_mem oneI_not_mem_zero hmem
  refine ⟨idMotive_spine, hne, fun e => hne ?_⟩
  have e' := appSpine_churchConst jRaw (churchTele_cinterp rd (jTypeC ()) Env.nil) (Nat.le_refl _)
    idMotive_spine
  rw [instPi_jType idMotive_spine, app_app_idMotive, oneI_type, appSpine_jRaw,
    whenTag_of_mem (refl_mem_tag bot)] at e'
  exact e'.symm.trans e

/-! ## Negative: the argument projections -/

/-- The function `λ y p. y`, not projected. -/
def yMotive : Ideal := lam fun Y => lam fun _ => principal Y

theorem app_app_yMotive (y p : Ideal) : app (app yMotive y) p = y := by
  have e : app yMotive y = lam fun _ => y := app_lam_principal (H := fun z => lam fun _ => z)
    (cont_lam_param fun _ => Cont.id) y
  rw [e, app_lam_const]

theorem univ_not_mem_projT_nat (I : Ideal) : ¬ (projT natI I).Mem (.tag .univ) :=
  ProjectionControls.univ_not_mem_projT_nat I

/-- The projection of `λ y p. y` onto the motive type over `U` and `num`. -/
def yMotiveProj : Ideal :=
  projT (cinterp rd motiveTypeC (Env.cons natI (Env.cons univIdeal Env.nil))) yMotive

/-- **Without the argument projections, the eliminator is not an element of its
declared type.** At `J U num (λ y p. y) U U (refl ⊥)` the method `U` is not an element
of `P num (refl num) = num`: the function without argument projections returns `U`,
and its projection onto the declared type returns an element without the universe
tag. -/
theorem jCod_not_typed : projT (jTypeI rd ()) jCod ≠ jCod := by
  intro h
  have hdom : app (app yMotiveProj natI) (Ideal.refl natI) = natI := by
    rw [yMotiveProj, app_app_motive, app_app_yMotive, natI_type, natI_type]
  have hargs : projArgs (jTypeI rd ()) [univIdeal, natI, yMotive, univIdeal, univIdeal, Ideal.refl bot] =
      [univIdeal, natI, yMotiveProj, projT natI univIdeal, univIdeal, Ideal.refl bot] := by
    refine (projArgs_cinterp_pi_of rd _ (y' := univIdeal) ?_).trans (congrArg (List.cons _) ?_)
    · exact univ_type
    refine (projArgs_cinterp_pi_of rd _ (y' := natI) ?_).trans (congrArg (List.cons _) ?_)
    · exact natI_type
    refine (projArgs_cinterp_pi_of rd _ (y' := yMotiveProj) ?_).trans (congrArg (List.cons _) ?_)
    · rfl
    refine (projArgs_cinterp_pi_of rd _ (y' := projT natI univIdeal) ?_).trans
      (congrArg (List.cons _) ?_)
    · show projT (app (app yMotiveProj natI) (Ideal.refl natI)) univIdeal = _
      rw [hdom]
    refine (projArgs_cinterp_pi_of rd _ (y' := univIdeal) ?_).trans (congrArg (List.cons _) ?_)
    · exact univ_type
    refine (projArgs_cinterp_pi_of rd [] (y' := Ideal.refl bot) ?_).trans rfl
    exact refl_bot_mem _ _ _
  have e := appSpine_projT jCod (churchTele_cinterp rd (jTypeC ()) Env.nil) (Nat.le_refl _)
    (args := [univIdeal, natI, yMotive, univIdeal, univIdeal, Ideal.refl bot])
  rw [h, hargs, appSpine_jCod, appSpine_jCod, app_app_yMotive,
    whenTag_of_mem (refl_mem_tag bot), whenTag_of_mem (refl_mem_tag bot), univ_type] at e
  have hu : univIdeal.Mem (.tag .univ) := ent_of_mem List.mem_cons_self
  rw [e] at hu
  exact univ_not_mem_projT_nat univIdeal (projT_le _ _ _ (projT_le _ _ _ hu))

/-! ## Negative: the argument facts are needed -/

/-- **The linear rule needs the spine facts about the arguments.** At
`J num 0 (λ y p. Id num y y) (refl 1) 1 (refl ⊥)`: the instantiated type is
`Id num 1 1`, the contractum `refl 1` is an element of it, the method `refl 1` is not
an element of its parameter type `Id num 0 0`, and the spine does not denote the
contractum. -/
theorem argument_facts_needed :
    instPi (jTypeI rd ()) [natI, zeroI, idMotive, Ideal.refl oneI, oneI, Ideal.refl bot] =
        Ideal.ident natI oneI oneI ∧
      projT (Ideal.ident natI oneI oneI) (Ideal.refl oneI) = Ideal.refl oneI ∧
      ¬ SpineTyped (jTypeI rd ()) [natI, zeroI, idMotive, Ideal.refl oneI, oneI, Ideal.refl bot] ∧
      appSpine (jConst rd ()) [natI, zeroI, idMotive, Ideal.refl oneI, oneI, Ideal.refl bot] ≠
        Ideal.refl oneI := by
  have h4 : projT (cinterp rd (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))
      (Env.cons idMotive (Env.cons zeroI (Env.cons natI Env.nil)))) (Ideal.refl oneI) =
        projT (Ideal.ident natI zeroI zeroI) (Ideal.refl oneI) := by
    show projT (app (app idMotive zeroI) (Ideal.refl zeroI)) (Ideal.refl oneI) = _
    rw [app_app_idMotive, projT_natI_zeroI]
  have hinst : instPi (jTypeI rd ()) [natI, zeroI, idMotive, Ideal.refl oneI, oneI, Ideal.refl bot] =
      Ideal.ident natI oneI oneI := by
    refine (instPi_cinterp_pi_of rd _ (y' := natI) ?_).trans ?_
    · exact natI_type
    refine (instPi_cinterp_pi_of rd _ (y' := zeroI) ?_).trans ?_
    · exact projT_natI_zeroI
    refine (instPi_cinterp_pi_of rd _ (y' := idMotive) ?_).trans ?_
    · exact projT_projT _ _
    refine (instPi_cinterp_pi_of rd _ h4).trans ?_
    refine (instPi_cinterp_pi_of rd _ (y' := oneI) ?_).trans ?_
    · exact oneI_type
    refine (instPi_cinterp_pi_of rd [] (y' := Ideal.refl bot) ?_).trans ?_
    · exact refl_bot_mem _ _ _
    show app (app idMotive oneI) (Ideal.refl bot) = _
    rw [app_app_idMotive, oneI_type]
  have hnot : ¬ (projT (Ideal.ident natI zeroI zeroI) (Ideal.refl oneI)).Mem (.arg .refl 0 [] (.tag .succ)) :=
    reflTag_not_mem zeroI_not_mem_succ
  have hone : (Ideal.refl oneI).Mem (.arg .refl 0 [] (.tag .succ)) := mem_refl_arg (succI_mem_succ zeroI)
  refine ⟨hinst, refl_one_mem, fun spine => ?_, fun e => ?_⟩
  · obtain ⟨-, s1⟩ := (spineTyped_cinterp_pi rd _ _ _ _ _).1 spine
    obtain ⟨-, s2⟩ := (spineTyped_cinterp_pi rd _ _ _ _ _).1 s1
    obtain ⟨-, s3⟩ := (spineTyped_cinterp_pi rd _ _ _ _ _).1 s2
    obtain ⟨h, -⟩ := (spineTyped_cinterp_pi rd _ _ _ _ _).1 s3
    rw [h4] at h
    rw [← h] at hone
    exact hnot hone
  · have hargs : projArgs (jTypeI rd ()) [natI, zeroI, idMotive, Ideal.refl oneI, oneI, Ideal.refl bot] =
        [natI, zeroI, idMotive, projT (Ideal.ident natI zeroI zeroI) (Ideal.refl oneI), oneI,
          Ideal.refl bot] :=
      by
        refine (projArgs_cinterp_pi_of rd _ (y' := natI) ?_).trans (congrArg (List.cons _) ?_)
        · exact natI_type
        refine (projArgs_cinterp_pi_of rd _ (y' := zeroI) ?_).trans (congrArg (List.cons _) ?_)
        · exact projT_natI_zeroI
        refine (projArgs_cinterp_pi_of rd _ (y' := idMotive) ?_).trans (congrArg (List.cons _) ?_)
        · exact projT_projT _ _
        refine (projArgs_cinterp_pi_of rd _ h4).trans (congrArg (List.cons _) ?_)
        refine (projArgs_cinterp_pi_of rd _ (y' := oneI) ?_).trans (congrArg (List.cons _) ?_)
        · exact oneI_type
        refine (projArgs_cinterp_pi_of rd [] (y' := Ideal.refl bot) ?_).trans rfl
        exact refl_bot_mem _ _ _
    have e' := appSpine_projT jRaw (churchTele_cinterp rd (jTypeC ()) Env.nil) (Nat.le_refl _)
      (args := [natI, zeroI, idMotive, Ideal.refl oneI, oneI, Ideal.refl bot])
    rw [hargs, appSpine_jRaw, whenTag_of_mem (refl_mem_tag bot)] at e'
    have hv : (appSpine (jConst rd ()) [natI, zeroI, idMotive, Ideal.refl oneI, oneI,
        Ideal.refl bot]).Mem (.arg .refl 0 [] (.tag .succ)) := by rw [e]; exact hone
    change (appSpine (projT (jTypeI rd ()) jRaw) _).Mem _ at hv
    rw [e'] at hv
    exact hnot (projT_le _ _ _ hv)

/-! ## Positive: numeral recursion at closed arguments -/

/-- The motive `λ _. num`. -/
def constMotive : Ideal := projT (cinterp rd (.pi (.const nm.num) (.head nm.univ)) Env.nil) (lam fun _ => natI)

theorem app_constMotive (v : Ideal) : app constMotive v = natI := by
  rw [constMotive, app_projT_cinterp_pi, app_lam_const]
  exact natI_type

/-- The method `λ v r. suc r`. -/
def sucMethod : Ideal :=
  projT (cinterp rd (nrStepTypeC nm) (Env.cons zeroI (Env.cons constMotive Env.nil)))
    (lam fun _ => lam fun R => succI (principal R))

theorem app_app_sucMethod (v r : Ideal) : app (app sucMethod v) r = succI (projT natI r) := by
  unfold sucMethod nrStepTypeC
  rw [app_projT_cinterp_pi, app_projT_cinterp_pi]
  show projT (app constMotive (app (rd.const nm.suc) (projT (rd.const nm.num) v)))
      (app (app (lam fun _ => lam fun R => succI (principal R)) (projT (rd.const nm.num) v))
        (projT (app constMotive (projT (rd.const nm.num) v)) r)) = _
  rw [app_constMotive, app_constMotive, app_lam_const, app_lam_principal cont_succI]
  exact projT_natI_succI (projT_projT _ _)

theorem numRec_spine {x : Ideal} (hx : projT natI x = x) :
    SpineTyped (nrTypeI rd nm) [constMotive, zeroI, sucMethod, x] :=
  (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨projT_projT _ _,
    (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨by
        show projT (app constMotive (rd.const nm.zero)) zeroI = zeroI
        rw [app_constMotive, projT_natI_zeroI],
      (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨projT_projT _ _,
        (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨by
            show projT (rd.const nm.num) x = x
            rw [rd_num, hx], trivial⟩⟩⟩⟩

theorem numRec_prefix : SpineTyped (nrTypeI rd nm) [constMotive, zeroI, sucMethod] :=
  ((spineTyped_append (args := [constMotive, zeroI, sucMethod]) (args' := [zeroI])).1
    (numRec_spine projT_natI_zeroI)).1

/-- **Positive**: `num-rec (λ _. num) 0 (λ v r. suc r) 0` denotes `0`. -/
theorem numRec_closed_zero : appSpine (nrConst rd nm) [constMotive, zeroI, sucMethod, zeroI] = zeroI := by
  have spine := numRec_spine projT_natI_zeroI
  refine nrConst_iotaZero ⟨rfl, spine⟩ ?_
  rw [instPi_nr numRec_prefix, rd_num, projT_natI_zeroI, app_constMotive, projT_natI_zeroI]

/-- **Positive**: `num-rec (λ _. num) 0 (λ v r. suc r) (suc 0)` denotes `1`, by the
successor rule. -/
theorem numRec_closed_succ :
    appSpine (nrConst rd nm) [constMotive, zeroI, sucMethod, app (sucConst rd nm) zeroI] = oneI := by
  have hsuc : app (sucConst rd nm) zeroI = oneI := by
    rw [app_sucConst rd nm rd_num, projT_natI_zeroI]
    rfl
  have spine : SpineTyped (nrTypeI rd nm) [constMotive, zeroI, sucMethod, app (sucConst rd nm) zeroI] := by
    rw [hsuc]
    exact numRec_spine oneI_type
  have hr : app (app sucMethod zeroI) (appSpine (nrConst rd nm) [constMotive, zeroI, sucMethod, zeroI]) =
      oneI := by
    rw [numRec_closed_zero, app_app_sucMethod, projT_natI_zeroI]
    rfl
  rw [nrConst_iotaSucc rd_num ⟨rfl, spine⟩ ?_, hr]
  rw [hr, instPi_nr numRec_prefix, rd_num, hsuc, oneI_type, app_constMotive, oneI_type]

/-! ## Negative: the decoding of an equation needs the contractum's typing -/

/-- **The decoding of an equation code needs the contractum's typing.** At the carrier
`num` and the endpoints `U`, `Id num U U` is not a type, and `holds (eq@num U U)`
denotes something other than `Id num U U`: the equation code projects its endpoints
onto the carrier. -/
theorem decode_eq_needs_right :
    projT univIdeal (Ideal.ident natI univIdeal univIdeal) ≠ Ideal.ident natI univIdeal univIdeal ∧
      app holdsConst (appSpine (eqConst natI) [univIdeal, univIdeal]) ≠
        Ideal.ident natI univIdeal univIdeal := by
  have hu : univIdeal.Mem (.tag .univ) := ent_of_mem List.mem_cons_self
  have hmem : (Ideal.ident natI univIdeal univIdeal).Mem (.arg .ident 1 [] (.tag .univ)) :=
    subset_closure (.inr (.inr (.inl ⟨[], _, rfl, fun _ h => absurd h List.not_mem_nil, hu⟩)))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have e := (typeGenerated_ident_endpoints (projT_univ_eq_self_iff.1 h)).1
    rw [← e] at hu
    exact univ_not_mem_projT_nat univIdeal hu
  · rw [← h, app_holdsConst, appSpine_eqConst] at hmem
    exact univ_not_mem_projT_nat univIdeal
      ((mem_ident_arg (projT_le _ _ _ (projT_le _ _ _ (projT_le _ _ _ hmem)))).2.1 rfl)

end EliminatorControls
end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
