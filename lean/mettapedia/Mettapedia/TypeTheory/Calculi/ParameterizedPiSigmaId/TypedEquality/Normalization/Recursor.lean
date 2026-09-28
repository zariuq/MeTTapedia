import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.InductiveSemantics

/-!
# The recursor of a simple inductive type is semantic

At reducibly equal scrutinees, reducibly equal motives and reducibly equal
methods, the full applications of the recursor are reducibly equal at the
motive applied to the scrutinee. The proof inducts on the reducible equality of
the scrutinees:

- a scrutinee reduces to its weak-head normal form, and the motive applied to
  the two has the same pack;
- at a constructor, the recursor computes to the method applied to the fields
  and to the recursive calls at the recursive fields, which are reducibly equal
  by induction; a method applied to reducibly equal arguments gives reducibly
  equal results, binder by binder;
- at a neutral scrutinee, the application is stuck, neutral and convertible.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst liftClosed_zero)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## Methods and hypotheses -/

/-- Reducibly equal methods, one for each constructor, over the motive `p`. -/
inductive MethodsEq (S : Setting Head L) {n : Nat} (Δ : Ctx Head n) (T : DeclName) (p : Tm Head n) :
    List (DeclName × List (Field Head)) → List (Tm Head n) → List (Tm Head n) → Prop
  | nil : MethodsEq S Δ T p [] [] []
  | cons {k : DeclName} {fields : List (Field Head)} {cs : List (DeclName × List (Field Head))}
      {m m' : Tm Head n} {ms ms' : List (Tm Head n)}
      (reducible : Reducible S Δ (caseType T k fields p) (packOf S Δ (caseType T k fields p)))
      (equal : (packOf S Δ (caseType T k fields p)).eqTm m m')
      (tail : MethodsEq S Δ T p cs ms ms') :
      MethodsEq S Δ T p ((k, fields) :: cs) (m :: ms) (m' :: ms')

theorem MethodsEq.snoc {n : Nat} {Δ : Ctx Head n} {T : DeclName} {p : Tm Head n}
    {k : DeclName} {fields : List (Field Head)} {m m' : Tm Head n}
    (reducible : Reducible S Δ (caseType T k fields p) (packOf S Δ (caseType T k fields p)))
    (equal : (packOf S Δ (caseType T k fields p)).eqTm m m') :
    ∀ {cs : List (DeclName × List (Field Head))} {ms ms' : List (Tm Head n)},
      MethodsEq S Δ T p cs ms ms' → MethodsEq S Δ T p (cs ++ [(k, fields)]) (ms ++ [m]) (ms' ++ [m'])
  | _, _, _, .nil => .cons reducible equal .nil
  | _, _, _, .cons r e tail => .cons r e (MethodsEq.snoc reducible equal tail)

theorem MethodsEq.length {n : Nat} {Δ : Ctx Head n} {T : DeclName} {p : Tm Head n} :
    ∀ {cs : List (DeclName × List (Field Head))} {ms ms' : List (Tm Head n)},
      MethodsEq S Δ T p cs ms ms' → ms.length = cs.length ∧ ms'.length = cs.length
  | _, _, _, .nil => ⟨rfl, rfl⟩
  | _, _, _, .cons _ _ tail => by
      have h := MethodsEq.length tail
      exact ⟨by simp [h.1], by simp [h.2]⟩

theorem MethodsEq.get {n : Nat} {Δ : Ctx Head n} {T : DeclName} {p : Tm Head n} :
    ∀ {cs : List (DeclName × List (Field Head))} {ms ms' : List (Tm Head n)},
      MethodsEq S Δ T p cs ms ms' → ∀ {i : Nat} {k : DeclName} {fields : List (Field Head)},
      cs[i]? = some (k, fields) → ∃ m m', ms[i]? = some m ∧ ms'[i]? = some m' ∧
        Reducible S Δ (caseType T k fields p) (packOf S Δ (caseType T k fields p)) ∧
        (packOf S Δ (caseType T k fields p)).eqTm m m'
  | _, _, _, .nil, _, _, _, h => by simp at h
  | _, _, _, .cons (m := m) (m' := m') r e tail, i, _, _, h => by
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨m, m', rfl, rfl, r, e⟩
      | succ i =>
          simp only [List.getElem?_cons_succ] at h ⊢
          exact MethodsEq.get tail h

/-- Reducibly equal induction hypotheses over the motive `p`. -/
inductive HypsEq (S : Setting Head L) {n : Nat} (Δ : Ctx Head n) (p : Tm Head n) :
    List (Tm Head n) → List (Tm Head n) → List (Tm Head n) → Prop
  | nil : HypsEq S Δ p [] [] []
  | cons {r ih ih' : Tm Head n} {rs ihs ihs' : List (Tm Head n)}
      (equal : (packOf S Δ (.app p r)).eqTm ih ih') (tail : HypsEq S Δ p rs ihs ihs') :
      HypsEq S Δ p (r :: rs) (ih :: ihs) (ih' :: ihs')

section Application

variable (laws : S.E.Laws S.R S.roles) {n : Nat} {Δ : Ctx Head n} (formed : CtxFormed S.R Δ)
include laws formed

/-- A motive `T → v` at reducibly equal motives and arguments: the application
is a reducible type, with the same pack at both. -/
theorem motive_apps {T : DeclName} {v : Head} (hv : S.R.isUniverse v) {PF : Pack Head n}
    (rF : Reducible S Δ (.pi (.const T) (.head v)) PF) {p p' : Tm Head n} (hpp : PF.eqTm p p')
    {a b : Tm Head n} (ha : (packOf S Δ (.const T)).redTm a) (hb : (packOf S Δ (.const T)).redTm b)
    (hab : (packOf S Δ (.const T)).eqTm a b) :
    Reducible S Δ (.app p a) (packOf S Δ (.app p a)) ∧
      (packOf S Δ (.app p a)).eqTy (.app p' b) ∧
      packOf S Δ (.app p a) = packOf S Δ (.app p' b) := by
  obtain ⟨parts, same, _⟩ := Reducible.pi_view laws rF
  rw [same] at hpp
  have e₁ := parts.app_eqTm laws formed hpp ha hb hab
  change (packOf S Δ (.head v)).eqTm _ _ at e₁
  have rU := (universe_logRel (S := S) hv formed).reducible
  rw [← rU.eq_packOf laws] at e₁
  obtain ⟨_, ⟨Q, lower⟩, eqTy⟩ := universe_equal laws hv formed e₁
  obtain ⟨_, member'⟩ := rU.eqTm_redTm laws e₁
  obtain ⟨Q', lower'⟩ := universePack_redTm_logRel (LevelOrder.lt_succ _) member'
  have r₁ := lower.reducible.packOf_self laws
  exact ⟨r₁, eqTy, r₁.conv laws (lower'.reducible.packOf_self laws) eqTy⟩

/-- A function of the induction hypotheses, applied to reducibly equal
hypotheses. -/
theorem caseHyps_app {p target : Tm Head n} :
    ∀ {rs ihs ihs' : List (Tm Head n)}, HypsEq S Δ p rs ihs ihs' → ∀ {g g' : Tm Head n},
      Reducible S Δ (caseHyps p rs target) (packOf S Δ (caseHyps p rs target)) →
      (packOf S Δ (caseHyps p rs target)).eqTm g g' →
      Reducible S Δ (.app p target) (packOf S Δ (.app p target)) ∧
        (packOf S Δ (.app p target)).eqTm (appSpine g ihs) (appSpine g' ihs')
  | _, _, _, .nil, g, g', r, h => by
      rw [caseHyps_nil] at r h
      exact ⟨r, h⟩
  | _, _, _, .cons (r := x) (ih := ih) (ih' := ih') equal tail, g, g', r, h => by
      rw [caseHyps_cons] at r h
      obtain ⟨parts, same, _⟩ := Reducible.pi_view laws r
      rw [same] at h
      have rDom := parts.dom_self formed
      obtain ⟨hih, hih'⟩ := rDom.eqTm_redTm laws equal
      have e := parts.app_eqTm laws formed h hih hih' equal
      have rCod := parts.cod_self formed hih
      rw [inst0_caseHyps] at e rCod
      exact caseHyps_app tail rCod e

/-- A method applied to reducibly equal arguments for its fields. -/
theorem caseFields_app {T k : DeclName} {ctors : List (DeclName × List (Field Head))}
    (hT : packOf S Δ (.const T) = indPack S Δ T ctors fun F => packOf S Δ (liftClosed F)) :
    ∀ {as : List (Tm Head n)} {fs : List (Field Head)} {as' : List (Tm Head n)},
      IndEqFields S Δ T ctors (fun F => packOf S Δ (liftClosed F)) fs as as' →
      ∀ {p : Tm Head n} {xs recs : List (Tm Head n)} {m m' : Tm Head n},
      Reducible S Δ (caseFields T k fs p xs recs) (packOf S Δ (caseFields T k fs p xs recs)) →
      (packOf S Δ (caseFields T k fs p xs recs)).eqTm m m' →
      Reducible S Δ (caseHyps p (recs ++ recArgs fs as) (appSpine (.const k) (xs ++ as)))
          (packOf S Δ (caseHyps p (recs ++ recArgs fs as) (appSpine (.const k) (xs ++ as)))) ∧
        (packOf S Δ (caseHyps p (recs ++ recArgs fs as) (appSpine (.const k) (xs ++ as)))).eqTm
          (appSpine m as) (appSpine m' as')
  | [], _, _, h, p, xs, recs, m, m', r, e => by
      cases h
      simp only [caseFields, recArgs, List.append_nil, appSpine_nil] at r e ⊢
      exact ⟨r, e⟩
  | a :: as, _, _, h, p, xs, recs, m, m', r, e => by
      cases h with
      | @recursive fs _ as' _ a' head tail =>
          simp only [caseFields] at r e
          obtain ⟨parts, same, _⟩ := Reducible.pi_view laws r
          rw [same] at e
          have rDom := parts.dom_self formed
          have head' : (packOf S Δ (.const T)).eqTm a a' := by rw [hT]; exact head
          obtain ⟨ha, ha'⟩ := rDom.eqTm_redTm laws head'
          have e₁ := parts.app_eqTm laws formed e ha ha' head'
          have rCod := parts.cod_self formed ha
          have inst := inst0_caseFields T k fs a p xs recs [.var 0] [a] rfl
          rw [inst] at e₁ rCod
          have result := caseFields_app hT tail rCod e₁
          simp only [List.append_assoc, List.singleton_append] at result
          exact result
      | @closed fs _ as' F _ a' head tail =>
          simp only [caseFields] at r e
          obtain ⟨parts, same, _⟩ := Reducible.pi_view laws r
          rw [same] at e
          have rDom := parts.dom_self formed
          obtain ⟨ha, ha'⟩ := rDom.eqTm_redTm laws head
          have e₁ := parts.app_eqTm laws formed e ha ha' head
          have rCod := parts.cod_self formed ha
          have inst := inst0_caseFields T k fs a p xs recs [] [] rfl
          rw [List.append_nil, List.append_nil] at inst
          rw [inst] at e₁ rCod
          have result := caseFields_app hT tail rCod e₁
          simp only [List.append_assoc, List.singleton_append] at result
          exact result

end Application

/-! ## The recursor's telescope -/

/-- The telescope of the motive and the methods. -/
abbrev recPrefix (T : DeclName) (v : Head) (ctors : List (DeclName × List (Field Head))) :
    Ctx Head (ctors.length + 1) :=
  ofEntries (recEntry T v ctors) (ctors.length + 1)

/-- The recursor applied to the motive and the methods of a substitution of its
prefix. -/
def recHead (rec T : DeclName) (v : Head) (ctors : List (DeclName × List (Field Head))) {m : Nat}
    (τ : Sub Head (ctors.length + 1) m) : Tm Head m :=
  applyClosed (recPrefix T v ctors) τ (.const rec)

theorem app_recHead (rec T : DeclName) (v : Head) (ctors : List (DeclName × List (Field Head)))
    {m : Nat} (τ : Sub Head (ctors.length + 1) m) (t : Tm Head m) :
    Tm.app (recHead rec T v ctors τ) t = recApp rec (telescopeArgs (recPrefix T v ctors) τ) t := by
  rw [recHead, applyClosed_eq_appSpine, recApp, appSpine_concat]

/-- A root step as a typed reduction. -/
theorem RedTm.of_root {n : Nat} {Γ : Ctx Head n} {src tgt X : Tm Head n}
    (step : S.R.computation.step src tgt) (source : Typed S.R Γ src X)
    (target : Typed S.R Γ tgt X) : RedTm S.R S.roles Γ src tgt X :=
  ⟨.single (.root step), source, target, .root step source target⟩

theorem inst0_motiveApp {n : Nat} (p x : Tm Head n) :
    inst0 x (.app (Presentation.rename wk p) (.var 0)) = .app p x := by
  show Tm.app (inst0 x (Presentation.rename wk p)) x = _
  rw [inst0_rename_wk]

section Prefix

variable (laws : S.E.Laws S.R S.roles) {m : Nat} {Δ : Ctx Head m} {T : DeclName} {v : Head}
  {ctors : List (DeclName × List (Field Head))}
include laws

/-- The motive and the methods of validly equal substitutions of the prefix
telescope. -/
theorem methods_of_eqSubst :
    ∀ (j : Nat), j ≤ ctors.length → ∀ {τ τ' : Sub Head (j + 1) m},
      EqSubst S (ofEntries (recEntry T v ctors) (j + 1)) Δ τ τ' →
      Reducible S Δ (.pi (.const T) (.head v)) (packOf S Δ (.pi (.const T) (.head v))) ∧
      (packOf S Δ (.pi (.const T) (.head v))).eqTm (τ (Fin.last j)) (τ' (Fin.last j)) ∧
      ∃ ms ms', telescopeArgs (ofEntries (recEntry T v ctors) (j + 1)) τ = τ (Fin.last j) :: ms ∧
        telescopeArgs (ofEntries (recEntry T v ctors) (j + 1)) τ' = τ' (Fin.last j) :: ms' ∧
        MethodsEq S Δ T (τ (Fin.last j)) (ctors.take j) ms ms' := by
  intro j
  induction j with
  | zero =>
      intro _ τ τ' e
      obtain ⟨_, Q, rQ, eQ⟩ := e
      change Reducible S Δ (.pi (.const T) (.head v)) Q at rQ
      rw [rQ.eq_packOf laws] at eQ
      exact ⟨rQ.packOf_self laws, eQ, [], [], rfl, rfl, .nil⟩
  | succ j ih =>
      intro hj τ τ' e
      obtain ⟨tail, Q, rQ, eQ⟩ := e
      obtain ⟨rMotive, motive, ms, ms', hms, hms', methods⟩ := ih (by omega) tail
      have hget : ctors[j]? = some ctors[j] := List.getElem?_eq_getElem (by omega)
      rcases hc : ctors[j] with ⟨k, fields⟩
      rw [hc] at hget
      rw [recEntry_method T v ctors hget, subst_caseType] at rQ
      change Reducible S Δ (caseType T k fields (τ (Fin.last (j + 1)))) Q at rQ
      rw [rQ.eq_packOf laws] at eQ
      refine ⟨rMotive, motive, ms ++ [τ 0], ms' ++ [τ' 0], ?_, ?_, ?_⟩
      · rw [telescopeArgs_ofEntries_succ, hms]
        rfl
      · rw [telescopeArgs_ofEntries_succ, hms']
        rfl
      · rw [List.take_succ_eq_append_getElem (by omega), hc]
        exact methods.snoc (rQ.packOf_self laws) eQ

end Prefix

section Typing

variable {m : Nat} {Δ : Ctx Head m} {T : DeclName} {v : Head}
  {ctors : List (DeclName × List (Field Head))} {rec : DeclName} {R₀ R₁ R₂ : Rules Head} {u : Head}
  (decl : DeclaresInductive S R₀ R₁ R₂ T u ctors rec v)
include decl

/-- The recursor at its declared type, in every context. -/
theorem DeclaresInductive.rec_typing {n : Nat} {Γ : Ctx Head n} :
    Typed S.R Γ (.const rec) (liftClosed (recType T v ctors)) := by
  obtain ⟨w, hw, typed⟩ := decl.recTyped
  exact .const decl.recDeclared (Derivable.mono decl.sub₂ typed) hw

/-- The recursor applied to a typed motive and typed methods. -/
theorem DeclaresInductive.prefix_typing {τ : Sub Head (ctors.length + 1) m}
    (typed : SubstMor S.R (recPrefix T v ctors) Δ τ) :
    Typed S.R Δ (recHead rec T v ctors τ)
      (.pi (.const T) (.app (Presentation.rename wk (τ (Fin.last ctors.length))) (.var 0))) := by
  have h := Typed.telescope_apply (Θ := recPrefix T v ctors)
    (X := .pi (recEntry T v ctors (ctors.length + 1)) (recBody ctors.length)) typed
    (decl.rec_typing (Γ := Δ))
  rw [recEntry_scrutinee] at h
  exact h

/-- The full application of the recursor to a typed scrutinee. -/
theorem DeclaresInductive.app_typing {τ : Sub Head (ctors.length + 1) m}
    (typed : SubstMor S.R (recPrefix T v ctors) Δ τ) {t : Tm Head m}
    (ht : Typed S.R Δ t (.const T)) :
    Typed S.R Δ (.app (recHead rec T v ctors τ) t) (.app (τ (Fin.last ctors.length)) t) := by
  have h := Derivable.appElim (decl.prefix_typing typed) ht
  rwa [inst0_motiveApp] at h

/-- Reducing the scrutinee of a full application of the recursor. -/
theorem DeclaresInductive.scrutinee_red {τ : Sub Head (ctors.length + 1) m}
    (typed : SubstMor S.R (recPrefix T v ctors) Δ τ) {t nf X : Tm Head m}
    (red : RedTm S.R S.roles Δ t nf (.const T))
    (result : TypeEq S.R Δ (.app (τ (Fin.last ctors.length)) t) X)
    (resultNf : TypeEq S.R Δ (.app (τ (Fin.last ctors.length)) nf) X) :
    RedTm S.R S.roles Δ (.app (recHead rec T v ctors τ) t) (.app (recHead rec T v ctors τ) nf) X := by
  have prefixTyping := decl.prefix_typing typed
  have source := Derivable.appElim prefixTyping red.source
  have target := Derivable.appElim prefixTyping red.target
  have equal := Derivable.appCong (.refl prefixTyping) red.equal
  rw [inst0_motiveApp] at source target equal
  refine ⟨?_, Typed.convType source result, Typed.convType target resultNf,
    Equal.convType equal result⟩
  have role : S.roles rec = .computes (ctors.length + 2)
      (.split (telescopeArgs (recPrefix T v ctors) τ).length .constructor fun _ => .leaf) := by
    rw [telescopeArgs_length]
    exact decl.recRole
  have w := WhRed.scrutinee (before := telescopeArgs (recPrefix T v ctors) τ) (after := []) role
    (by rw [telescopeArgs_length]; rfl) red.red
  rw [app_recHead, app_recHead, recApp, recApp]
  exact w

/-- The recursor applied to convertible motives and methods has convertible
head spines. -/
theorem DeclaresInductive.head_convNe (laws : S.E.Laws S.R S.roles) {τ τ' : Sub Head (ctors.length + 1) m}
    (conv : ∀ i, S.E.convTm Δ (τ i) (τ' i)
      (Presentation.subst τ (Ctx.lookup (recPrefix T v ctors) i))) :
    S.E.convNe Δ (recHead rec T v ctors τ) (recHead rec T v ctors τ')
      (.pi (.const T) (.app (Presentation.rename wk (τ (Fin.last ctors.length))) (.var 0))) := by
  have h := convNe_telescope_apply laws (Θ := recPrefix T v ctors)
    (X := .pi (recEntry T v ctors (ctors.length + 1)) (recBody ctors.length)) conv
    (laws.convNe_const rec (decl.rec_typing (Γ := Δ)))
  rw [recEntry_scrutinee] at h
  exact h

end Typing

/-! ## Computation at reducible scrutinees -/

section Rel

variable (laws : S.E.Laws S.R S.roles) {m : Nat} {Δ : Ctx Head m} (formed : CtxFormed S.R Δ)
  {T : DeclName} {v : Head} {ctors : List (DeclName × List (Field Head))} {rec : DeclName}
  {R₀ R₁ R₂ : Rules Head} {u : Head} (decl : DeclaresInductive S R₀ R₁ R₂ T u ctors rec v)
include laws formed decl

/-- At validly equal substitutions of the recursor's prefix, reducibly equal
scrutinees give reducibly equal full applications. -/
theorem DeclaresInductive.rec_rel {τ τ' : Sub Head (ctors.length + 1) m}
    (vτ : ValidSubst S (recPrefix T v ctors) Δ τ) (vτ' : ValidSubst S (recPrefix T v ctors) Δ τ')
    (e : EqSubst S (recPrefix T v ctors) Δ τ τ') {t t' : Tm Head m}
    (equal : IndEqTm S Δ T ctors (fun F => packOf S Δ (liftClosed F)) t t') :
    (packOf S Δ (.app (τ (Fin.last ctors.length)) t)).eqTm
      (.app (recHead rec T v ctors τ) t) (.app (recHead rec T v ctors τ') t') := by
  have typed := vτ.substMor laws
  have typed' := vτ'.substMor laws
  obtain ⟨rMotive, motiveEq, ms, ms', hms, hms', methods⟩ :=
    methods_of_eqSubst laws ctors.length (Nat.le_refl _) e
  rw [List.take_length] at methods
  have hT := decl.packOf_type laws formed
  have rT := decl.type_reducible laws formed
  have fieldEnds : ∀ {F}, IsClosedField ctors F → ∀ {a b},
      (packOf S Δ (liftClosed F)).eqTm a b →
      (packOf S Δ (liftClosed F)).redTm a ∧ (packOf S Δ (liftClosed F)).redTm b :=
    fun ⟨_, _, mem, closed⟩ _ _ h =>
      (decl.field_logRel laws formed mem closed).reducible.eqTm_redTm laws h
  have convτ : ∀ i, S.E.convTm Δ (τ i) (τ' i)
      (Presentation.subst τ (Ctx.lookup (recPrefix T v ctors) i)) := by
    intro i
    obtain ⟨Q, rQ, eQ⟩ := e.lookup i
    exact (rQ.escape laws).eqTm eQ
  have headsRA : recApp rec (τ (Fin.last ctors.length) :: ms) =
      Tm.app (recHead rec T v ctors τ) := by
    funext x
    rw [app_recHead, hms]
  have headsRA' : recApp rec (τ' (Fin.last ctors.length) :: ms') =
      Tm.app (recHead rec T v ctors τ') := by
    funext x
    rw [app_recHead, hms']
  have lengths := methods.length
  refine IndEqTm.rec
    (motive_1 := fun t t' _ => (packOf S Δ (.app (τ (Fin.last ctors.length)) t)).eqTm
      (.app (recHead rec T v ctors τ) t) (.app (recHead rec T v ctors τ') t'))
    (motive_2 := fun nf nf' _ => Typed S.R Δ nf (.const T) → Typed S.R Δ nf' (.const T) →
      S.E.convTm Δ nf nf' (.const T) →
      (packOf S Δ (.app (τ (Fin.last ctors.length)) nf)).eqTm
        (.app (recHead rec T v ctors τ) nf) (.app (recHead rec T v ctors τ') nf'))
    (motive_3 := fun fs as as' _ => HypsEq S Δ (τ (Fin.last ctors.length)) (recArgs fs as)
      ((recArgs fs as).map (.app (recHead rec T v ctors τ)))
      ((recArgs fs as').map (.app (recHead rec T v ctors τ'))))
    ?mk ?ctor ?neutral ?nil ?recursive ?closed equal
  case mk =>
    intro t t' nf nf' red red' conv normal ih
    obtain ⟨nfNormal, nfNormal'⟩ := IndEqNf.ends laws fieldEnds normal
    have hnf : (packOf S Δ (.const T)).redTm nf := by
      rw [hT]
      exact .mk (RedTm.refl red.target) (laws.convTm_trans conv (laws.convTm_symm conv)) nfNormal
    have hnf' : (packOf S Δ (.const T)).redTm nf' := by
      rw [hT]
      exact .mk (RedTm.refl red'.target) (laws.convTm_trans (laws.convTm_symm conv) conv)
        nfNormal'
    have hEq : (packOf S Δ (.const T)).eqTm t t' := by
      rw [hT]
      exact .mk red red' conv normal
    obtain ⟨ht, ht'⟩ := rT.eqTm_redTm laws hEq
    obtain ⟨_, htnf⟩ := rT.redTm_expand red hnf
    obtain ⟨_, ht'nf'⟩ := rT.redTm_expand red' hnf'
    have htnf' := rT.eqTm_trans laws hEq ht'nf'
    obtain ⟨rApp, _, sameNf⟩ :=
      motive_apps laws formed decl.hv rMotive (rMotive.reflexive.eqTm
        (rMotive.eqTm_redTm laws motiveEq).1) ht hnf htnf
    obtain ⟨_, eqT', _⟩ := motive_apps laws formed decl.hv rMotive motiveEq ht ht' hEq
    obtain ⟨_, eqNf', _⟩ := motive_apps laws formed decl.hv rMotive motiveEq ht hnf' htnf'
    obtain ⟨_, eqNf, _⟩ :=
      motive_apps laws formed decl.hv rMotive (rMotive.reflexive.eqTm
        (rMotive.eqTm_redTm laws motiveEq).1) ht hnf htnf
    have escape := rApp.escape laws
    have toT' := laws.convTy_sound (escape.eqTy eqT')
    have toNf' := laws.convTy_sound (escape.eqTy eqNf')
    have toNf := laws.convTy_sound (escape.eqTy eqNf)
    have redL := decl.scrutinee_red typed red (laws.convTy_sound escape.refl) toNf.symm
    have redR := decl.scrutinee_red typed' red' toT'.symm toNf'.symm
    have inner := ih red.target red'.target conv
    rw [← sameNf] at inner
    exact rApp.eqTm_expand laws redL redR inner
  case ctor =>
    intro k fields as as' mem arguments ih ty ty' conv
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp mem
    obtain ⟨mt, mt', hm, hm', rCase, eCase⟩ := methods.get hi
    obtain ⟨lenAs, lenAs'⟩ := arguments.length
    obtain ⟨rHyps, eHyps⟩ :=
      caseFields_app laws formed hT arguments (xs := []) (recs := []) rCase eCase
    simp only [List.nil_append] at rHyps eHyps
    obtain ⟨rRes, eRes⟩ := caseHyps_app laws formed ih rHyps eHyps
    have step := decl.iota (p := τ (Fin.last ctors.length)) lengths.1 hi lenAs hm
    have step' := decl.iota (p := τ' (Fin.last ctors.length)) lengths.2 hi lenAs' hm'
    rw [headsRA, appSpine_append] at step
    rw [headsRA', appSpine_append] at step'
    have hEq : (packOf S Δ (.const T)).eqTm (appSpine (.const k) as) (appSpine (.const k) as') := by
      rw [hT]
      exact .mk (RedTm.refl ty) (RedTm.refl ty') conv (.ctor mem arguments)
    obtain ⟨hk, hk'⟩ := rT.eqTm_redTm laws hEq
    obtain ⟨_, eqK, _⟩ := motive_apps laws formed decl.hv rMotive motiveEq hk hk' hEq
    have toK := laws.convTy_sound ((rRes.escape laws).eqTy eqK)
    obtain ⟨hres, hres'⟩ := rRes.eqTm_redTm laws eRes
    have red₁ := RedTm.of_root step (decl.app_typing typed ty) ((rRes.escape laws).redTm hres).1
    have red₁' := RedTm.of_root step' (Typed.convType (decl.app_typing typed' ty') toK.symm)
      ((rRes.escape laws).redTm hres').1
    exact rRes.eqTm_expand laws red₁ red₁' eRes
  case neutral =>
    intro nf nf' nN nN' convN ty ty' conv
    have hEq : (packOf S Δ (.const T)).eqTm nf nf' := by
      rw [hT]
      exact .mk (RedTm.refl ty) (RedTm.refl ty') conv (.neutral nN nN' convN)
    obtain ⟨hn, hn'⟩ := rT.eqTm_redTm laws hEq
    obtain ⟨rApp, eqN, _⟩ := motive_apps laws formed decl.hv rMotive motiveEq hn hn' hEq
    have toN := laws.convTy_sound ((rApp.escape laws).eqTy eqN)
    have role : ∀ {τ₀ : Sub Head (ctors.length + 1) m}, S.roles rec = .computes (ctors.length + 2)
        (.split (telescopeArgs (recPrefix T v ctors) τ₀).length .constructor fun _ => .leaf) := by
      intro τ₀
      rw [telescopeArgs_length]
      exact decl.recRole
    have lengthOk : ∀ {τ₀ : Sub Head (ctors.length + 1) m},
        (telescopeArgs (recPrefix T v ctors) τ₀).length + 1 + ([] : List (Tm Head m)).length =
          ctors.length + 2 := by
      intro τ₀
      rw [telescopeArgs_length]
      rfl
    have neutralL : Neutral S.roles (.app (recHead rec T v ctors τ) nf) := by
      rw [app_recHead, recApp]
      exact .stuck_single (after := []) role lengthOk nN
    have neutralR : Neutral S.roles (.app (recHead rec T v ctors τ') nf') := by
      rw [app_recHead, recApp]
      exact .stuck_single (after := []) role lengthOk nN'
    have spine := laws.convNe_app (decl.head_convNe laws convτ)
      (laws.convTm_of_convNe (.inl nN) (.inl nN') convN)
    rw [inst0_motiveApp] at spine
    exact (rApp.reflects laws).eqTm neutralL neutralR (decl.app_typing typed ty)
      (Typed.convType (decl.app_typing typed' ty') toN.symm) spine
  case nil => exact .nil
  case recursive =>
    intro fields as as' a a' head tail ih₁ ih₃
    exact .cons ih₁ ih₃
  case closed =>
    intro fields as as' F a a' head tail ih₃
    exact ih₃

end Rel

/-! ## The recursor is semantic -/

section Semantics

variable (laws : S.E.Laws S.R S.roles) {T : DeclName} {v : Head}
  {ctors : List (DeclName × List (Field Head))} {rec : DeclName} {R₀ R₁ R₂ : Rules Head} {u : Head}
  (decl : DeclaresInductive S R₀ R₁ R₂ T u ctors rec v)
include laws decl

/-- The declared type of the recursor is a valid term of a universe. -/
theorem DeclaresInductive.rec_valid_type :
    ∃ w, S.R.isUniverse w ∧ ValidTm S .nil (recType T v ctors) (.head w) := by
  obtain ⟨w, hw, typed⟩ := decl.recTyped
  exact ⟨w, hw, Derivable.valid_sub laws decl.sub₂
    (AllSemantic.semanticConstantsOf (decl.semantic₂ laws)) typed trivial⟩

/-- The full application of the recursor is valid in its telescope. -/
theorem DeclaresInductive.rec_full :
    ValidTm S (recTele T v ctors) (applyClosed (recTele T v ctors) ids (.const rec))
      (recBody ctors.length) := by
  obtain ⟨w, hw, validType⟩ := decl.rec_valid_type laws
  obtain ⟨_, validBody⟩ := ValidTy.telescope laws (recTele T v ctors) (validType.validTy laws hw)
  have apply : ∀ {m : Nat} (σ : Sub Head (ctors.length + 2) m),
      Presentation.subst σ (applyClosed (recTele T v ctors) ids (.const rec)) =
        .app (recHead rec T v ctors (tailSub σ)) (σ 0) := by
    intro m σ
    rw [applyClosed_subst]
    rfl
  have core : ∀ {m : Nat} {Δ : Ctx Head m} {σ σ' : Sub Head (ctors.length + 2) m},
      ValidSubst S (recTele T v ctors) Δ σ → ValidSubst S (recTele T v ctors) Δ σ' →
      EqSubst S (recTele T v ctors) Δ σ σ' →
      ∀ {P : Pack Head m}, Reducible S Δ (Presentation.subst σ (recBody ctors.length)) P →
        P.eqTm (Presentation.subst σ (applyClosed (recTele T v ctors) ids (.const rec)))
          (Presentation.subst σ' (applyClosed (recTele T v ctors) ids (.const rec))) := by
    intro m Δ σ σ' vσ vσ' e P r
    obtain ⟨vτ, _⟩ := vσ
    obtain ⟨vτ', _⟩ := vσ'
    obtain ⟨eτ, Q, rQ, eQ⟩ := e
    have formed := vτ.formed
    rw [recEntry_scrutinee] at rQ
    change Reducible S Δ (.const T) Q at rQ
    rw [rQ.eq_packOf laws, decl.packOf_type laws formed] at eQ
    have h := decl.rec_rel laws formed vτ vτ' eτ eQ
    rw [apply, apply]
    change Reducible S Δ (.app (σ (Fin.last (ctors.length + 1))) (σ 0)) P at r
    rw [r.eq_packOf laws]
    exact h
  exact ⟨validBody, fun vσ P r => (r.eqTm_redTm laws (core vσ vσ vσ.refl r)).1,
    fun vσ vσ' e P r => core vσ vσ' e r⟩

/-- The recursor is a semantic constant. -/
theorem DeclaresInductive.rec_semantic : SemanticConstant S rec (recType T v ctors) := by
  obtain ⟨w, hw, validType⟩ := decl.rec_valid_type laws
  have typing : Typed S.R .nil (.const rec) (closeType (recTele T v ctors) (recBody ctors.length)) := by
    have h := decl.rec_typing (Γ := .nil)
    rwa [liftClosed_zero] at h
  show SemanticConstant S rec (closeType (recTele T v ctors) (recBody ctors.length))
  exact SemanticConstant.of_telescope laws (.inr ⟨_, decl.recRole⟩) (Θ := recTele T v ctors)
    (C := recBody ctors.length) typing (validType.validTy laws hw) (decl.rec_full laws)

/-- Every constant of a declared simple inductive type is semantic: the type,
its constructors and its recursor. -/
theorem DeclaresInductive.semantic :
    SemanticConstant S T (.head u) ∧
      (∀ {k : DeclName} {fields : List (Field Head)}, (k, fields) ∈ ctors →
        SemanticConstant S k (ctorType T fields)) ∧
      SemanticConstant S rec (recType T v ctors) :=
  ⟨decl.type_semantic laws, fun mem => decl.ctor_semantic laws mem, decl.rec_semantic laws⟩

end Semantics

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
