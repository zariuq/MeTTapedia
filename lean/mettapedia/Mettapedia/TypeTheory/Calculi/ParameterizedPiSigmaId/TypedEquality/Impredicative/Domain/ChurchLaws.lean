import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Eliminators

/-!
# Laws of the interpretation of annotated terms

**Functions and dependent types that carry their domain** (`Ideal.clam`,
`Ideal.cpi`, `Ideal.csigma`) are determined by their values at the elements of
the domain (`Ideal.clam_ext`, `Ideal.cpi_ext`, `Ideal.csigma_ext`). For a
continuous body and family:

* **β**: applying `clam A H` to `y` is `H` at the projection of `y` onto `A`
  (`Ideal.app_clam`);
* **the projection onto `cpi A G`** is the function carrying the domain `A` whose
  value at `y` is the value at `y` projected onto `G y` (`Ideal.projT_cpi`); so a
  function carrying its domain is an element of `cpi A G` when its body sends
  elements of `A` to elements of the family (`Ideal.semTyped_clam`), and
  **η** holds for every element of `cpi A G` (`Ideal.clam_app_of_mem`);
* **the projection onto `csigma A G`** is the pair of the projection of the first
  component onto `A` and the projection of the second onto the family at the
  projected first component (`Ideal.projT_csigma`); so a pair of elements is an
  element (`Ideal.semTyped_pair`), both projections of an element are elements
  (`Ideal.semTyped_fst`, `Ideal.semTyped_snd`), and **η** holds for every element
  of `csigma A G` (`Ideal.pair_fst_snd_of_mem`). The pair of two least elements is
  the least element (`Ideal.pair_bot`), the η-collapse of pairs.

**Type generation.** The domain and the family values of a type-generated
dependent type are type-generated (`Ideal.typeGenerated_dom`,
`Ideal.typeGenerated_fam`), and a dependent type carrying its domain is
type-generated when its domain is and its family is at every element of the
domain (`Ideal.typeGenerated_cpi`, `Ideal.typeGenerated_csigma`).

**Identity types.** Reflexivity at an element of the carrier is an element of every
identity type whose endpoints are above the point (`Ideal.semTyped_refl`); an
identity type determines its endpoints (`Ideal.ident_endpoints_eq`); the point of
a reflexivity is read back by `Ideal.reflPoint` (`Ideal.reflPoint_refl`).

**Continuity.** Iterated application and the instantiation of a dependent function
type are continuous in the function and in each argument (`Ideal.cont_appSpine_fun`,
`Ideal.cont_appSpine_arg`, `Ideal.cont_instPi_type`, `Ideal.cont_instPi_arg`), and
so is the projection onto the instantiated type (`Ideal.cont₂_projT_instPi`).

**The interpretation** commutes with renaming and simultaneous substitution
(`cinterp_rename`, `cinterp_subst`), so with opening a binder (`cinterp_inst0`)
and with closed terms (`cinterp_liftClosed`); β for annotated abstractions holds
at every argument (`app_cinterp_lam`), and the projections onto the interpretations
of `Π A B` and `Σ A B` decompose along `A` and `B` (`projT_cinterp_pi`,
`projT_cinterp_sigma`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain

open Annotated (CTm CSub)

namespace Ideal

variable {A : Ideal} {G G' : Ideal → Ideal}

/-! ## Extensionality -/

/-- A function carrying its domain is determined by its values at the elements of
the domain. -/
theorem clam_ext {K K' : Ideal → Ideal} (h : ∀ y, projT A y = y → K y = K' y) :
    clam A K = clam A K' := by
  unfold clam
  congr 1
  funext X
  exact h _ (projT_projT _ _)

/-- A dependent function type carrying its domain is determined by its family at
the elements of the domain. -/
theorem cpi_ext (h : ∀ y, projT A y = y → G y = G' y) : cpi A G = cpi A G' := by
  unfold cpi
  congr 1
  funext X
  exact h _ (projT_projT _ _)

/-- A dependent pair type carrying its domain is determined by its family at the
elements of the domain. -/
theorem csigma_ext (h : ∀ y, projT A y = y → G y = G' y) : csigma A G = csigma A G' := by
  unfold csigma
  congr 1
  funext X
  exact h _ (projT_projT _ _)

/-! ## Functions -/

/-- **β for functions that carry their domain**: applying `clam A H` to `y` is `H`
at the projection of `y` onto `A`. -/
theorem app_clam {H : Ideal → Ideal} (hH : Cont H) (y : Ideal) :
    app (clam A H) y = H (projT A y) :=
  app_lam_principal (H := fun z => H (projT A z)) (hH.comp (cont_projT A)) y

/-- **The projection onto a dependent function type that carries its domain** is the
function carrying the domain whose value at `y` is the value at `y`, projected onto
the family there. -/
theorem projT_cpi (hG : Cont G) (f : Ideal) :
    projT (cpi A G) f = clam A fun y => projT (G y) (app f y) := by
  have hF : Monotone fun X => G (projT A (principal X)) :=
    fun h => hG.mono (projT_mono (principal_mono h))
  rw [cpi, projT_pi hF]
  unfold clam piProj
  congr 1
  funext X
  have h := fam_cpi (A := A) hG (projT A (principal X))
  rw [projT_projT] at h
  exact congrArg (fun T => projT T (app f (projT A (principal X)))) h

/-- The projection of a function carrying its domain onto a dependent function type
over the same domain. -/
theorem projT_cpi_clam (hG : Cont G) {H : Ideal → Ideal} (hH : Cont H) :
    projT (cpi A G) (clam A H) = clam A fun y => projT (G y) (H y) := by
  rw [projT_cpi hG]
  exact clam_ext fun y hy => by rw [app_clam hH, hy]

/-- **A function carrying its domain is an element of a dependent function type over
the domain** when its body sends elements of the domain to elements of the family. -/
theorem semTyped_clam (hG : Cont G) {H : Ideal → Ideal} (hH : Cont H)
    (h : ∀ y, projT A y = y → projT (G y) (H y) = H y) :
    projT (cpi A G) (clam A H) = clam A H := by
  rw [projT_cpi_clam hG hH]
  exact clam_ext h

/-- **η for functions that carry their domain**: an element of `cpi A G` is the
function carrying the domain `A` whose value at `y` is its application to `y`. -/
theorem clam_app_of_mem (hG : Cont G) {f : Ideal} (hf : projT (cpi A G) f = f) :
    clam A (fun y => app f y) = f := by
  conv_rhs => rw [← hf, projT_cpi hG]
  exact clam_ext fun y hy => (semTyped_app hG hf hy).symm

/-! ## Pairs -/

theorem dom_csigma (A : Ideal) (G : Ideal → Ideal) : dom .sigma (csigma A G) = A :=
  dom_former _ _ _

/-- The family of `csigma A G` at `y` is `G` at the projection of `y`. -/
theorem fam_csigma (hG : Cont G) (y : Ideal) : fam .sigma (csigma A G) y = G (projT A y) :=
  fam_former_principal (k := .sigma) A (hG.comp (cont_projT A)) y

/-- **The projection onto a dependent pair type that carries its domain**: the first
component is projected onto the domain, and the second onto the family at the
projected first component. -/
theorem projT_csigma (hG : Cont G) (x : Ideal) :
    projT (csigma A G) x = pair (projT A (fst x)) (projT (G (projT A (fst x))) (snd x)) := by
  have hF : Monotone fun X => G (projT A (principal X)) :=
    fun h => hG.mono (projT_mono (principal_mono h))
  have h := projT_sigma (A := A) hF x
  rw [show (former .sigma A fun X => G (projT A (principal X))) = csigma A G from rfl,
    fam_csigma hG, projT_projT] at h
  exact h

/-- The projection of a pair onto a dependent pair type carrying its domain. -/
theorem projT_csigma_pair (hG : Cont G) (a b : Ideal) :
    projT (csigma A G) (pair a b) = pair (projT A a) (projT (G (projT A a)) b) := by
  rw [projT_csigma hG, fst_pair, snd_pair]

/-- **A pair of elements is an element** of a dependent pair type. -/
theorem semTyped_pair (hG : Cont G) {a b : Ideal} (ha : projT A a = a)
    (hb : projT (G a) b = b) : projT (csigma A G) (pair a b) = pair a b := by
  rw [projT_csigma_pair hG, ha, hb]

/-- The first projection of an element of a dependent pair type is an element of the
domain. -/
theorem semTyped_fst (hG : Cont G) {x : Ideal} (hx : projT (csigma A G) x = x) :
    projT A (fst x) = fst x := by
  have h := congrArg fst (projT_csigma (A := A) hG x)
  rw [hx, fst_pair] at h
  exact h.symm

/-- The second projection of an element of a dependent pair type is an element of the
family at the first projection. -/
theorem semTyped_snd (hG : Cont G) {x : Ideal} (hx : projT (csigma A G) x = x) :
    projT (G (fst x)) (snd x) = snd x := by
  have h := congrArg snd (projT_csigma (A := A) hG x)
  rw [hx, snd_pair, semTyped_fst hG hx] at h
  exact h.symm

/-- **η for pairs**: an element of a dependent pair type is the pair of its
projections. -/
theorem pair_fst_snd_of_mem (hG : Cont G) {x : Ideal} (hx : projT (csigma A G) x = x) :
    pair (fst x) (snd x) = x := by
  calc pair (fst x) (snd x) = projT (csigma A G) x := by
        rw [projT_csigma hG, semTyped_fst hG hx, semTyped_snd hG hx]
    _ = x := hx

/-- The least element has only trivial observations: it entails every generator of
the pair of two least elements. -/
theorem pair_bot : pair bot bot = bot := by
  refine le_antisymm (closure_le fun t ht => ?_) (bot_le _)
  rcases ht with ⟨s, rfl, hs⟩ | ⟨C, s, rfl, hC, hs⟩
  · show ent [] (.arg .pair 0 [] s) = true
    rw [ent_arg, List.all_nil, Bool.true_and]
    exact hs
  · show ent [] (.arg .pair 1 C s) = true
    rw [ent_arg, Bool.and_eq_true, List.all_eq_true]
    exact ⟨fun c hc => hC c hc, hs⟩

/-! ## Type generation -/

/-- **The domain of a type-generated dependent type is type-generated.** -/
theorem typeGenerated_dom {k : Kind} (hk : k = .pi ∨ k = .sigma) {T : Ideal}
    (hT : TypeGenerated T) : TypeGenerated (dom k T) := by
  refine typeGenerated_closure fun g hg => ?_
  obtain ⟨w, hw, hg'⟩ := hT _ hg
  rw [ent_arg, List.all_nil, Bool.true_and] at hg'
  exact ⟨args k 0 w, fun s hs => ⟨below_dom_args (fun r hr => (hw r hr).1) s hs,
    ty_args_dom hk (fun r hr => (hw r hr).2) s hs⟩, hg'⟩

/-- **The family values of a type-generated dependent type are type-generated.** -/
theorem typeGenerated_fam {k : Kind} (hk : k = .pi ∨ k = .sigma) {T : Ideal}
    (hT : TypeGenerated T) (y : Ideal) : TypeGenerated (fam k T y) := by
  refine typeGenerated_closure fun g ⟨C, Z, Y, hm, hZ, hg⟩ => ?_
  obtain ⟨w, hw, he⟩ := hT _ hm
  rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at he
  exact ⟨fnApp k w Z, fun s hs => ⟨below_fam_fnApp (fun r hr => (hw r hr).1) hZ s hs,
    ty_fnApp hk (fun r hr => (hw r hr).2) Z s hs⟩, he.2 g hg⟩

/-- A family that sees its argument through the projection onto `A` sees it only
through its typed observations. -/
theorem family_typedObservations (hG : Cont G) (X : List Tok) (t : Tok)
    (ht : (G (projT A (principal X))).Mem t) :
    ∃ w, w ⊑ X ∧ (∀ s ∈ w, TypedAt A s) ∧ (G (projT A (principal w))).Mem t := by
  obtain ⟨W, hW, htW⟩ := hG.finite ht
  obtain ⟨w, hw, hWw⟩ := below_closure_iff.1 hW
  refine ⟨w, fun s hs => (hw s hs).1, fun s hs => (hw s hs).2, hG.mono ?_ t htW⟩
  exact principal_le_iff.2 fun r hr => ⟨w, fun s hs => ⟨ent_of_mem hs, (hw s hs).2⟩, hWw r hr⟩

/-- **A dependent function type carrying its domain is type-generated** when its
domain is, and its family is at every element of the domain. -/
theorem typeGenerated_cpi (hG : Cont G) (hA : TypeGenerated A)
    (hGy : ∀ y, projT A y = y → TypeGenerated (G y)) : TypeGenerated (cpi A G) :=
  typeGenerated_former (.inl rfl) (fun h => hG.mono (projT_mono (principal_mono h))) hA
    (fun _ => hGy _ (projT_projT _ _)) (family_typedObservations hG)

/-- **A dependent pair type carrying its domain is type-generated** when its domain
is, and its family is at every element of the domain. -/
theorem typeGenerated_csigma (hG : Cont G) (hA : TypeGenerated A)
    (hGy : ∀ y, projT A y = y → TypeGenerated (G y)) : TypeGenerated (csigma A G) :=
  typeGenerated_former (.inr rfl) (fun h => hG.mono (projT_mono (principal_mono h))) hA
    (fun _ => hGy _ (projT_projT _ _)) (family_typedObservations hG)

theorem TypeGenerated.cpi_dom (h : TypeGenerated (cpi A G)) : TypeGenerated A := by
  have h' := typeGenerated_dom (.inl rfl) h
  rwa [dom_cpi] at h'

theorem TypeGenerated.cpi_fam (hG : Cont G) (h : TypeGenerated (cpi A G)) {y : Ideal}
    (hy : projT A y = y) : TypeGenerated (G y) := by
  have h' := typeGenerated_fam (.inl rfl) h y
  rwa [fam_cpi hG, hy] at h'

theorem TypeGenerated.csigma_dom (h : TypeGenerated (csigma A G)) : TypeGenerated A := by
  have h' := typeGenerated_dom (.inr rfl) h
  rwa [dom_csigma] at h'

theorem TypeGenerated.csigma_fam (hG : Cont G) (h : TypeGenerated (csigma A G)) {y : Ideal}
    (hy : projT A y = y) : TypeGenerated (G y) := by
  have h' := typeGenerated_fam (.inr rfl) h y
  rwa [fam_csigma hG, hy] at h'

/-! ## Identity types -/

/-- **Reflexivity at an element of the carrier is an element of an identity type**
whose endpoints are above the point. -/
theorem semTyped_refl {I J a : Ideal} (ha : projT A a = a) (hI : a ≤ I) (hJ : a ≤ J) :
    projT (ident A I J) (refl a) = refl a := by
  unfold refl
  refine projT_closure_eq fun g hg => ?_
  rcases hg with rfl | ⟨s, rfl, hs⟩
  · refine ⟨[.tag .refl], fun r hr => ?_, ent_of_mem List.mem_cons_self⟩
    rw [List.mem_singleton.1 hr]
    exact ⟨subset_closure (.inl rfl), [.tag .ident],
      fun t ht => by rw [List.mem_singleton.1 ht]; exact subset_closure (.inl rfl),
      Elem.ty_tag (k := .ident) trivial Elem.isUniv_univ, tyTok_tag_refl.2 List.mem_cons_self⟩
  · rw [← ha] at hs
    obtain ⟨w, hw, hsw⟩ := hs
    obtain ⟨c, hc, hcu, hwc⟩ := typedAt_list fun r hr => (hw r hr).2
    refine ⟨w.map (.arg .refl 0 []), fun r hr => ?_, ?_⟩
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      refine ⟨subset_closure (.inr ⟨r', rfl, (hw r' hr').1⟩), Elem.ident c w w, ?_,
        Elem.ty_ident Elem.isUniv_univ hcu hwc hwc, ?_⟩
      · intro t ht
        simp only [Elem.ident, List.mem_cons, List.mem_append, List.mem_map] at ht
        rcases ht with rfl | (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩
        · exact subset_closure (.inl rfl)
        · exact subset_closure (.inr (.inl ⟨d, rfl, hc d hd⟩))
        · exact subset_closure (.inr (.inr (.inl ⟨c, d, rfl, hc, hI d (hw d hd).1⟩)))
        · exact subset_closure (.inr (.inr (.inr ⟨c, d, rfl, hc, hJ d (hw d hd).1⟩)))
      · refine tyTok_reflPoint.2 ⟨List.mem_cons_self, rfl, ?_, ?_, ?_⟩
        · exact (hwc r' hr').mono (Le.of_subset fun d hd => mem_args_of_arg (C := [])
            (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_map_of_mem hd)))))
        · exact ent_of_mem (mem_args_of_arg (C := c) (List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hr')))))
        · exact ent_of_mem (mem_args_of_arg (C := c) (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_map_of_mem hr'))))
    · rw [ent_arg, List.all_nil, Bool.true_and, args_map_arg_same]
      exact hsw

theorem mem_ident_left_iff {I J : Ideal} {s : Tok} :
    (ident A I J).Mem (.arg .ident 1 [] s) ↔ I.Mem s :=
  ⟨fun h => (mem_ident_arg h).2.1 rfl, fun h =>
    subset_closure (.inr (.inr (.inl ⟨[], s, rfl, fun _ h => absurd h List.not_mem_nil, h⟩)))⟩

theorem mem_ident_right_iff {I J : Ideal} {s : Tok} :
    (ident A I J).Mem (.arg .ident 2 [] s) ↔ J.Mem s :=
  ⟨fun h => (mem_ident_arg h).2.2 rfl, fun h =>
    subset_closure (.inr (.inr (.inr ⟨[], s, rfl, fun _ h => absurd h List.not_mem_nil, h⟩)))⟩

/-- **An identity type determines its endpoints.** -/
theorem ident_endpoints_eq {A' I I' J J' : Ideal} (h : ident A I J = ident A' I' J') :
    I = I' ∧ J = J' := by
  constructor
  · refine ext fun s => ?_
    have e := congrArg (fun T => T.Mem (.arg .ident 1 [] s)) h
    simp only [mem_ident_left_iff] at e
    exact Iff.of_eq e
  · refine ext fun s => ?_
    have e := congrArg (fun T => T.Mem (.arg .ident 2 [] s)) h
    simp only [mem_ident_right_iff] at e
    exact Iff.of_eq e

/-- The point of a reflexivity: the components of its point tokens. -/
def reflPoint (p : Ideal) : Ideal := closure fun s => p.Mem (.arg .refl 0 [] s)

/-- The generators of a reflexivity have their point components in the point. -/
private theorem refl_gen_args {I : Ideal} {w : List Tok}
    (hw : ∀ s ∈ w, s = .tag .refl ∨ ∃ r, s = .arg .refl 0 [] r ∧ I.Mem r) :
    Below (args .refl 0 w) I := by
  intro c hc
  rcases mem_args_iff.1 hc with ⟨C, hC⟩ | ⟨-, t, ht, -, hd⟩
  · rcases hw _ hC with h | ⟨r, h, hr⟩
    · cases h
    · cases h
      exact hr
  · rcases hw _ ht with rfl | ⟨r, rfl, -⟩
    · cases hd
    · cases hd

/-- **The point of a reflexivity is read back.** -/
theorem reflPoint_refl (I : Ideal) : reflPoint (refl I) = I := by
  refine le_antisymm (closure_le fun s hs => ?_) fun s hs =>
    subset_closure (subset_closure (.inr ⟨s, rfl, hs⟩))
  obtain ⟨w, hw, h⟩ := hs
  rw [ent_arg, List.all_nil, Bool.true_and] at h
  exact (refl_gen_args hw).ent h

theorem cont_reflPoint : Cont reflPoint :=
  Cont.of_closure (P := fun I s => I.Mem (.arg .refl 0 [] s)) (fun h s hs => h _ hs)
    fun {_ s} hs => ⟨[.arg .refl 0 [] s], fun r hr => by rw [List.mem_singleton.1 hr]; exact hs,
      ent_of_mem List.mem_cons_self⟩

/-! ## Continuity of spines -/

/-- Iterated application is continuous in the function. -/
theorem cont_appSpine_fun : ∀ args : List Ideal, Cont fun f => appSpine f args
  | [] => Cont.id
  | a :: as => (cont_appSpine_fun as).comp (cont₂_app.left a)

/-- Iterated application is continuous in each argument. -/
theorem cont_appSpine_arg (f : Ideal) (as bs : List Ideal) :
    Cont fun y => appSpine f (as ++ y :: bs) := by
  have h : (fun y => appSpine f (as ++ y :: bs)) =
      fun y => appSpine (app (appSpine f as) y) bs := by
    funext y
    rw [appSpine_append]
    rfl
  rw [h]
  exact (cont_appSpine_fun bs).comp (cont₂_app.right _)

/-- **The instantiated type is continuous in the type.** -/
theorem cont_instPi_type : ∀ ys : List Ideal, Cont fun T => instPi T ys
  | [] => Cont.id
  | y :: ys => (cont_instPi_type ys).comp
      ((cont₂_fam .pi).comp Cont.id ((cont_projT_type y).comp (cont_dom .pi)))

/-- **The instantiated type is continuous in each argument.** -/
theorem cont_instPi_arg (T : Ideal) (as bs : List Ideal) :
    Cont fun y => instPi T (as ++ y :: bs) := by
  have h : (fun y => instPi T (as ++ y :: bs)) =
      fun y => instPi (fam .pi (instPi T as) (projT (dom .pi (instPi T as)) y)) bs := by
    funext y
    rw [instPi_append]
    rfl
  rw [h]
  exact (cont_instPi_type bs).comp ((cont_fam_arg .pi _).comp (cont_projT _))

/-- The projection onto the instantiated type is continuous in each argument and in
the projected element. -/
theorem cont₂_projT_instPi (T : Ideal) (as bs : List Ideal) :
    Cont₂ fun y r => projT (instPi T (as ++ y :: bs)) r :=
  ⟨fun r => (cont_projT_type r).comp (cont_instPi_arg T as bs), fun _ => cont_projT _⟩

end Ideal

/-! ## The interpretation under renaming and substitution -/

open Ideal

variable {Head : Type}

/-- **The interpretation of a renamed term** is the interpretation in the
environment read through the renaming. -/
theorem cinterp_rename (Rd : Reading Head) :
    ∀ {n m : Nat} (r : Ren n m) (t : CTm Head n) (ρ : Env m),
      cinterp Rd (t.rename r) ρ = cinterp Rd t (fun i => ρ (r i)) := by
  have cons : ∀ {n m : Nat} (r : Ren n m) (ρ : Env m) (y : Ideal),
      (fun i => Env.cons y ρ (liftRen r i)) = Env.cons y (fun i => ρ (r i)) := by
    intro n m r ρ y
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  intro n m r t ρ
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB =>
      show Ideal.cpi _ _ = Ideal.cpi _ _
      rw [ihA]
      congr 1
      funext y
      rw [ihB, cons]
  | sigma A B ihA ihB =>
      show Ideal.csigma _ _ = Ideal.csigma _ _
      rw [ihA]
      congr 1
      funext y
      rw [ihB, cons]
  | id A a b ihA iha ihb =>
      show Ideal.ident _ _ _ = Ideal.ident _ _ _
      rw [ihA, iha, ihb]
  | lam A b ihA ihb =>
      show Ideal.clam _ _ = Ideal.clam _ _
      rw [ihA]
      congr 1
      funext y
      rw [ihb, cons]
  | app f a ihf iha =>
      show Ideal.app _ _ = Ideal.app _ _
      rw [ihf, iha]
  | pair a b iha ihb =>
      show Ideal.pair _ _ = Ideal.pair _ _
      rw [iha, ihb]
  | fst p ih =>
      show Ideal.fst _ = Ideal.fst _
      rw [ih]
  | snd p ih =>
      show Ideal.snd _ = Ideal.snd _
      rw [ih]
  | refl a ih =>
      show Ideal.refl _ = Ideal.refl _
      rw [ih]

/-- The interpretation of a weakened term in an extended environment. -/
theorem cinterp_rename_wk (Rd : Reading Head) {n : Nat} (t : CTm Head n) (y : Ideal)
    (ρ : Env n) : cinterp Rd (t.rename wk) (Env.cons y ρ) = cinterp Rd t ρ :=
  cinterp_rename Rd wk t (Env.cons y ρ)

/-- **The interpretation of a substituted term** is the interpretation in the
environment of the interpretations of the substitution. -/
theorem cinterp_subst (Rd : Reading Head) :
    ∀ {n m : Nat} (σ : CSub Head n m) (t : CTm Head n) (ρ : Env m),
      cinterp Rd (t.subst σ) ρ = cinterp Rd t (fun i => cinterp Rd (σ i) ρ) := by
  have cons : ∀ {n m : Nat} (σ : CSub Head n m) (ρ : Env m) (y : Ideal),
      (fun i => cinterp Rd (CTm.liftSub σ i) (Env.cons y ρ)) =
        Env.cons y (fun i => cinterp Rd (σ i) ρ) := by
    intro n m σ ρ y
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact cinterp_rename_wk Rd (σ j) y ρ
  intro n m σ t ρ
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB =>
      show Ideal.cpi _ _ = Ideal.cpi _ _
      rw [ihA]
      congr 1
      funext y
      rw [ihB, cons]
  | sigma A B ihA ihB =>
      show Ideal.csigma _ _ = Ideal.csigma _ _
      rw [ihA]
      congr 1
      funext y
      rw [ihB, cons]
  | id A a b ihA iha ihb =>
      show Ideal.ident _ _ _ = Ideal.ident _ _ _
      rw [ihA, iha, ihb]
  | lam A b ihA ihb =>
      show Ideal.clam _ _ = Ideal.clam _ _
      rw [ihA]
      congr 1
      funext y
      rw [ihb, cons]
  | app f a ihf iha =>
      show Ideal.app _ _ = Ideal.app _ _
      rw [ihf, iha]
  | pair a b iha ihb =>
      show Ideal.pair _ _ = Ideal.pair _ _
      rw [iha, ihb]
  | fst p ih =>
      show Ideal.fst _ = Ideal.fst _
      rw [ih]
  | snd p ih =>
      show Ideal.snd _ = Ideal.snd _
      rw [ih]
  | refl a ih =>
      show Ideal.refl _ = Ideal.refl _
      rw [ih]

/-- **Opening a binder** is interpreting its body with the argument's value. -/
theorem cinterp_inst0 (Rd : Reading Head) {n : Nat} (a : CTm Head n) (b : CTm Head (n + 1))
    (ρ : Env n) : cinterp Rd (CTm.inst0 a b) ρ = cinterp Rd b (Env.cons (cinterp Rd a ρ) ρ) := by
  unfold CTm.inst0
  rw [cinterp_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- A closed term denotes its value in the empty environment. -/
theorem cinterp_liftClosed (Rd : Reading Head) {n : Nat} (t : CTm Head 0) (ρ : Env n) :
    cinterp Rd (CTm.liftClosed t : CTm Head n) ρ = cinterp Rd t Env.nil := by
  unfold CTm.liftClosed
  rw [cinterp_rename]
  congr 1
  funext i
  exact i.elim0

/-! ## The interpretation of abstractions, dependent types and pairs -/

/-- **β for annotated abstractions**, at every argument: applying the interpretation
of `λ (x : A). b` to `y` is interpreting `b` at the projection of `y` onto the
interpretation of `A`. -/
theorem app_cinterp_lam (Rd : Reading Head) {n : Nat} (A : CTm Head n) (b : CTm Head (n + 1))
    (ρ : Env n) (y : Ideal) :
    app (cinterp Rd (.lam A b) ρ) y = cinterp Rd b (Env.cons (projT (cinterp Rd A ρ) y) ρ) :=
  app_clam (cinterp_cont_cons Rd b ρ) y

/-- The projection onto the interpretation of `Π A B`. -/
theorem projT_cinterp_pi (Rd : Reading Head) {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1))
    (ρ : Env n) (f : Ideal) :
    projT (cinterp Rd (.pi A B) ρ) f =
      clam (cinterp Rd A ρ) fun y => projT (cinterp Rd B (Env.cons y ρ)) (app f y) :=
  projT_cpi (cinterp_cont_cons Rd B ρ) f

theorem dom_cinterp_sigma (Rd : Reading Head) {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1))
    (ρ : Env n) : dom .sigma (cinterp Rd (.sigma A B) ρ) = cinterp Rd A ρ :=
  dom_csigma _ _

/-- The family of the interpretation of `Σ A B` at `y` is the interpretation of `B` at
the projection of `y` onto the interpretation of `A`. -/
theorem fam_cinterp_sigma (Rd : Reading Head) {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1))
    (ρ : Env n) (y : Ideal) :
    fam .sigma (cinterp Rd (.sigma A B) ρ) y =
      cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) y) ρ) :=
  fam_csigma (cinterp_cont_cons Rd B ρ) y

/-- The projection onto the interpretation of `Σ A B`. -/
theorem projT_cinterp_sigma (Rd : Reading Head) {n : Nat} (A : CTm Head n)
    (B : CTm Head (n + 1)) (ρ : Env n) (x : Ideal) :
    projT (cinterp Rd (.sigma A B) ρ) x =
      pair (projT (cinterp Rd A ρ) (fst x))
        (projT (cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (fst x)) ρ)) (snd x)) :=
  projT_csigma (cinterp_cont_cons Rd B ρ) x

end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
