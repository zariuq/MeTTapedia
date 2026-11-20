import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntaxDeclarations

/-!
# Typed syntax in the cumulative tower: the recursion principle and the model's hypotheses

* `at-num` and `at-bool`, the transports along the computed equations of the index, by recursion on
  the object type: at the matching type the value is returned; at the other type the proof is an
  element of the empty type, eliminated by its recursor.
* `syntax-rec`, the recursion principle of typed expressions, by structural recursion on the untyped
  expression; each right-hand side is typed after its match, where the typing relation computes the
  shape of the proof.
* Every declared constant is semantic, at every generic equality with the laws (`constantsAt`); every
  equation preserves typing (`roots`); with the head and level facts, every hypothesis of the
  normalization model holds for the package.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ)
open TowerVectorsModel (unit tt unitRec void voidRec add unitCtors U0 numC zeroC succC unitC ttC
  addC unitRecC voidC voidRecC TowerLike)

namespace TowerSyntaxModel

variable (lv : LevelExpr Nat)

/-! ## The empty type's recursor in a stage -/

section VoidRec

variable {R : Rules Tower.Head} (tw : TowerLike R)
include tw

theorem voidRecType_typed' (dVoid : R.constantType void = some (.head u)) :
    ∃ w, R.isUniverse w ∧ Typed R .nil (recType void (.sort lv) []) (.head w) := by
  have tVoid : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed R Δ voidC U0 := fun {_ _} => tw.small dVoid
  have tM : Typed R .nil (.pi voidC (.head (.sort lv))) (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm tVoid (tw.isUniverse _) (.headType (tw.headTyping _)) (tw.isUniverse _) (tw.join _ _)
  have tP : Typed R (.snoc (.snoc .nil (.pi voidC (.head (.sort lv)))) voidC) (.var 1)
      (.pi voidC (.head (.sort lv))) := .var 1
  have t₀ : Typed R (.snoc (.snoc .nil (.pi voidC (.head (.sort lv)))) voidC) (.var 0) voidC := .var 0
  have tBody : Typed R (.snoc (.snoc .nil (.pi voidC (.head (.sort lv)))) voidC) (.app (.var 1) (.var 0))
      (.head (.sort lv)) := .appElim tP t₀
  have t₂ := Derivable.piForm tVoid (tw.isUniverse _) tBody (tw.isUniverse _) (tw.join _ _)
  have t₁ := Derivable.piForm tM (tw.isUniverse _) t₂ (tw.isUniverse _) (tw.join _ _)
  exact ⟨_, tw.isUniverse _, t₁⟩

/-- `void-rec M t : M t`. -/
theorem voidRec_app_typed (dVoid : R.constantType void = some (.head u))
    (dRec : R.constantType voidRec = some (recType void (.sort lv) [])) {m : Nat} {Δ : Ctx Tower.Head m}
    {M t : Tm Tower.Head m} (tM : Typed R Δ M (.pi voidC (.head (.sort lv)))) (tt' : Typed R Δ t voidC) :
    Typed R Δ (voidRecC M t) (.app M t) := by
  obtain ⟨w, hw, typed⟩ := voidRecType_typed' lv tw dVoid
  have tc : Typed R Δ (.const voidRec) (liftClosed (recType void (.sort lv) [])) := .const dRec typed hw
  have m₀ : SubstMor R .nil Δ fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor R (recTele void (.sort lv) []) Δ (consSub t (consSub M fun i => Fin.elim0 i)) :=
    SubstMor.cons (SubstMor.cons m₀ tM) tt'
  exact Typed.telescope_apply mor tc

end VoidRec

/-! ## The transports -/

/-- The transports' type, for the constructor `c` and the equation family `f`. -/
abbrev atTypeOf (c f : DeclName) : Tm Tower.Head 0 :=
  .pi (.pi tyC U0) (.pi (.app (.var 0) (.const c)) (.pi tyC (.pi (.app (.const f) (.var 0))
    (.app (.var 3) (.var 1)))))

theorem tw_at : TowerLike (atStage lv) := towerLike_restrict lv _

theorem atType_typed {c f : DeclName} (dc : (atStage lv).constantType c = some (ctorType ty []))
    (df : (atStage lv).constantType f = some tyFamType) :
    ∃ w, (rules lv).isUniverse w ∧ Typed (atStage lv) .nil (atTypeOf c f) (.head w) := by
  have tw := tw_at lv
  have tTy : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed (atStage lv) Δ tyC U0 := fun {_ _} => tw.small rfl
  have tc : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed (atStage lv) Δ (.const c) tyC :=
    fun {_ _} => .const dc tTy (tw.isUniverse _)
  have tf : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed (atStage lv) Δ (.const f) (.pi tyC U0) :=
    fun {_ _} => .const df (tyFamily_typed tw rfl) (tw.isUniverse _)
  let Γ₁ : Ctx Tower.Head 1 := .snoc .nil (.pi tyC U0)
  have tQc : Typed (atStage lv) Γ₁ (.app (.var 0) (.const c)) U0 := .appElim (A := tyC) (B := U0) (.var 0) tc
  let Γ₂ : Ctx Tower.Head 2 := .snoc Γ₁ (.app (.var 0) (.const c))
  let Γ₃ : Ctx Tower.Head 3 := .snoc Γ₂ tyC
  have tFt : Typed (atStage lv) Γ₃ (.app (.const f) (.var 0)) U0 := .appElim (A := tyC) (B := U0) tf (.var 0)
  let Γ₄ : Ctx Tower.Head 4 := .snoc Γ₃ (.app (.const f) (.var 0))
  have tQt : Typed (atStage lv) Γ₄ (.app (.var 3) (.var 1)) U0 := .appElim (A := tyC) (B := U0) (.var 3) (.var 1)
  have t₃ := tw.pi_small tFt tQt
  have t₂ := tw.pi_small (tTy (Δ := Γ₂)) t₃
  have t₁ := tw.pi_small tQc t₂
  exact ⟨_, tw.isUniverse _, .piForm (tyFamily_typed tw rfl) (tw.isUniverse _) t₁ (tw.isUniverse _)
    (tw.join _ _)⟩

/-- The context of a transport's equation: `Q`, `x : Q c`, `u : f d`. -/
abbrev atCtx (c f d : DeclName) : Ctx Tower.Head 3 :=
  .snoc (.snoc (.snoc .nil (.pi tyC U0)) (.app (.var 0) (.const c))) (.app (.const f) (.const d))

theorem at_formed {c f d : DeclName} (dc : (atStage lv).constantType c = some (ctorType ty []))
    (dd : (atStage lv).constantType d = some (ctorType ty []))
    (df : (atStage lv).constantType f = some tyFamType) : CtxFormed (atStage lv) (atCtx c f d) := by
  have tw := tw_at lv
  have tTy : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed (atStage lv) Δ tyC U0 := fun {_ _} => tw.small rfl
  have tf : Typed (atStage lv) (.snoc (.snoc .nil (.pi tyC U0)) (.app (.var 0) (.const c))) (.const f)
      (.pi tyC U0) := .const df (tyFamily_typed tw rfl) (tw.isUniverse _)
  exact .snoc (.snoc (.snoc .nil ⟨_, tw.isUniverse _, tyFamily_typed tw rfl⟩)
    ⟨_, tw.isUniverse _, .appElim (A := tyC) (B := U0) (.var 0) (.const dc tTy (tw.isUniverse _))⟩)
    ⟨_, tw.isUniverse _, .appElim (A := tyC) (B := U0) tf (.const dd tTy (tw.isUniverse _))⟩

/-- At the other type, the transport eliminates the proof of the empty type. -/
theorem at_void_typed {c f d : DeclName} (_dc : (atStage lv).constantType c = some (ctorType ty []))
    (dd : (atStage lv).constantType d = some (ctorType ty []))
    (df : (atStage lv).constantType f = some tyFamType)
    (step : (rules lv).computation.step (.app (.const f) (.const d) : Tm Tower.Head 3) voidC) :
    Typed (atStage lv) (atCtx c f d) (voidRecC (.lam (.app (.var 3) (.const d))) (.var 0))
      (.app (.var 2) (.const d)) := by
  have tw := tw_at lv
  have tTy : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed (atStage lv) Δ tyC U0 := fun {_ _} => tw.small rfl
  have td : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed (atStage lv) Δ (.const d) tyC :=
    fun {_ _} => .const dd tTy (tw.isUniverse _)
  have tFd : Typed (atStage lv) (atCtx c f d) (.app (.const f) (.const d)) U0 :=
    .appElim (A := tyC) (B := U0) (.const df (tyFamily_typed tw rfl) (tw.isUniverse _)) td
  have eq : Equal (atStage lv) (atCtx c f d) (.app (.const f) (.const d)) voidC U0 :=
    .root step tFd (tw.small rfl)
  have tu₀ : Typed (atStage lv) (atCtx c f d) (.var 0) (.app (.const f) (.const d)) := .var 0
  have tu : Typed (atStage lv) (atCtx c f d) (.var 0) voidC := Typed.convType tu₀ ⟨_, tw.isUniverse _, eq⟩
  have tQ₄ : Typed (atStage lv) (.snoc (atCtx c f d) voidC) (.var 3) (.pi tyC U0) := .var 3
  have tQd : Typed (atStage lv) (.snoc (atCtx c f d) voidC) (.app (.var 3) (.const d)) (.head (.sort lv)) :=
    tw.lift (.appElim (A := tyC) (B := U0) tQ₄ td) lv
  have tMty : Typed (atStage lv) (atCtx c f d) (.pi voidC (.head (.sort lv)))
      (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm (tw.small rfl) (tw.isUniverse _) (.headType (tw.headTyping _)) (tw.isUniverse _) (tw.join _ _)
  have tM : Typed (atStage lv) (atCtx c f d) (.lam (.app (.var 3) (.const d))) (.pi voidC (.head (.sort lv))) :=
    .lamIntro tMty (tw.isUniverse _) tQd
  have tRec := voidRec_app_typed lv tw rfl rfl tM tu
  have beta : Equal (atStage lv) (atCtx c f d) (.app (.lam (.app (.var 3) (.const d))) (.var 0))
      (.app (.var 2) (.const d)) (.head (.sort lv)) :=
    .betaPi tMty (tw.isUniverse _) tQd tu
  exact Typed.convType tRec ⟨_, tw.isUniverse _, beta⟩

section Declarations

variable (valuation : Nat → Nat) {E : GenericEquality Tower.Head} (lawsE : E.Laws (rules lv) roles)
include lawsE

/-- The stage of the transports is semantic. -/
theorem semantic_at : AllSemantic (settingAt lv valuation E) (atStage lv) := by
  refine allSemantic_restrict lv fun name mem type declared => ?_
  rcases List.mem_cons.mp mem with rfl | mem
  · cases declared
    exact (declaresVoid lv valuation).rec_semantic lawsE
  exact semantic_typing lv valuation lawsE (by rw [restrict_of_mem lv mem]; exact declared)

/-- **The package declares `at-num`**: `at-num Q x tnum u ⟶ x`, and at `tbool` the proof is empty. -/
theorem declaresAtNum :
    DeclaresRecursion (settingAt lv valuation E) (atStage lv) atNum ty tyCtors atNumEntries 2 1 atResult
      atNumBody where
  role := roles_atNum
  scrutinee := rfl
  declared := rfl
  sub₀ := sub_restrict lv _ (by decide)
  semantic₀ := semantic_at lv valuation lawsE
  typed := atType_typed lv (c := tnum) (f := isNum) rfl rfl
  formed := by
    intro k fields mem
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact at_formed lv (c := tnum) (f := isNum) (d := tnum) rfl rfl rfl
    · exact at_formed lv (c := tnum) (f := isNum) (d := tbool) rfl rfl rfl
  bodyTyped := by
    intro k fields mem
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Typed (atStage lv) (atCtx tnum isNum tnum) (.var 1) (.app (.var 2) tnumC)
      exact .var 1
    · exact at_void_typed lv (c := tnum) (f := isNum) (d := tbool) rfl rfl rfl (isNum_tbool_step lv)
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll mem_atNum ⟨_, _, σ, as, mem, has, rfl, rfl⟩

/-- **The package declares `at-bool`**: `at-bool Q x tbool u ⟶ x`, and at `tnum` the proof is empty. -/
theorem declaresAtBool :
    DeclaresRecursion (settingAt lv valuation E) (atStage lv) atBool ty tyCtors atBoolEntries 2 1 atResult
      atBoolBody where
  role := roles_atBool
  scrutinee := rfl
  declared := rfl
  sub₀ := sub_restrict lv _ (by decide)
  semantic₀ := semantic_at lv valuation lawsE
  typed := atType_typed lv (c := tbool) (f := isBool) rfl rfl
  formed := by
    intro k fields mem
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact at_formed lv (c := tbool) (f := isBool) (d := tnum) rfl rfl rfl
    · exact at_formed lv (c := tbool) (f := isBool) (d := tbool) rfl rfl rfl
  bodyTyped := by
    intro k fields mem
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact at_void_typed lv (c := tbool) (f := isBool) (d := tnum) rfl rfl rfl (isBool_tnum_step lv)
    · show Typed (atStage lv) (atCtx tbool isBool tbool) (.var 1) (.app (.var 2) tboolC)
      exact .var 1
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll mem_atBool ⟨_, _, σ, as, mem, has, rfl, rfl⟩

/-- The stage of the recursion principle is semantic. -/
theorem semantic_syn : AllSemantic (settingAt lv valuation E) (synStage lv) := by
  refine allSemantic_restrict lv fun name mem type declared => ?_
  rcases List.mem_cons.mp mem with rfl | mem
  · cases declared
    intro m Δ formed P r
    exact (declaresTyping lv valuation lawsE).semantic lawsE (declaresRaw lv valuation lawsE) formed r
  rcases List.mem_cons.mp mem with rfl | mem
  · cases declared
    intro m Δ formed P r
    exact (declaresAtNum lv valuation lawsE).semantic lawsE (declaresTy lv valuation) formed r
  rcases List.mem_cons.mp mem with rfl | mem
  · cases declared
    intro m Δ formed P r
    exact (declaresAtBool lv valuation lawsE).semantic lawsE (declaresTy lv valuation) formed r
  exact semantic_at lv valuation lawsE (by rw [restrict_of_mem lv mem]; exact declared)

end Declarations

/-! ## The recursion principle: typings in its stage -/

theorem tw_syn : TowerLike (synStage lv) := towerLike_restrict lv _

section SynTyping

variable {m : Nat} {Δ : Ctx Tower.Head m}

theorem syn_ty : Typed (synStage lv) Δ tyC U0 := (tw_syn lv).small (c := ty) rfl
theorem syn_raw : Typed (synStage lv) Δ rawC U0 := (tw_syn lv).small (c := raw) rfl
theorem syn_num : Typed (synStage lv) Δ numC U0 := (tw_syn lv).small (c := num) rfl
theorem syn_bool : Typed (synStage lv) Δ boolC U0 := (tw_syn lv).small (c := bool) rfl
theorem syn_tnum : Typed (synStage lv) Δ tnumC tyC :=
  .const (type := ctorType ty []) rfl (syn_ty lv) (LevelTower.IsUniverse.sort _)
theorem syn_tbool : Typed (synStage lv) Δ tboolC tyC :=
  .const (type := ctorType ty []) rfl (syn_ty lv) (LevelTower.IsUniverse.sort _)

theorem syn_typing_typed {r t : Tm Tower.Head m} (tr : Typed (synStage lv) Δ r rawC)
    (tt' : Typed (synStage lv) Δ t tyC) : Typed (synStage lv) Δ (typingC r t) U0 :=
  .appElim (A := tyC) (B := U0) (.appElim (A := rawC) (B := .pi tyC U0)
    (.const (type := .pi rawC (.pi tyC U0)) rfl
      (.piForm (syn_raw lv) (LevelTower.IsUniverse.sort _) (tyFamily_typed (tw_syn lv) rfl)
        (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)) (LevelTower.IsUniverse.sort _)) tr) tt'

theorem syn_isNum_typed {t : Tm Tower.Head m} (tt' : Typed (synStage lv) Δ t tyC) :
    Typed (synStage lv) Δ (isNumC t) U0 :=
  .appElim (A := tyC) (B := U0)
    (.const (type := .pi tyC U0) rfl (tyFamily_typed (tw_syn lv) rfl) (LevelTower.IsUniverse.sort _)) tt'

theorem syn_isBool_typed {t : Tm Tower.Head m} (tt' : Typed (synStage lv) Δ t tyC) :
    Typed (synStage lv) Δ (isBoolC t) U0 :=
  .appElim (A := tyC) (B := U0)
    (.const (type := .pi tyC U0) rfl (tyFamily_typed (tw_syn lv) rfl) (LevelTower.IsUniverse.sort _)) tt'

theorem syn_rnum_typed {k : Tm Tower.Head m} (tk : Typed (synStage lv) Δ k numC) :
    Typed (synStage lv) Δ (rnumC k) rawC :=
  .appElim (A := numC) (B := rawC)
    (.const (type := .pi numC rawC) rfl ((tw_syn lv).pi_small (syn_num lv) (syn_raw lv))
      (LevelTower.IsUniverse.sort _)) tk

theorem syn_rbool_typed {b : Tm Tower.Head m} (tb : Typed (synStage lv) Δ b boolC) :
    Typed (synStage lv) Δ (rboolC b) rawC :=
  .appElim (A := boolC) (B := rawC)
    (.const (type := .pi boolC rawC) rfl ((tw_syn lv).pi_small (syn_bool lv) (syn_raw lv))
      (LevelTower.IsUniverse.sort _)) tb

theorem syn_radd_typed {a b : Tm Tower.Head m} (ta : Typed (synStage lv) Δ a rawC)
    (tb : Typed (synStage lv) Δ b rawC) : Typed (synStage lv) Δ (raddC a b) rawC :=
  .appElim (A := rawC) (B := rawC) (.appElim (A := rawC) (B := .pi rawC rawC)
    (.const (type := .pi rawC (.pi rawC rawC)) rfl
      ((tw_syn lv).pi_small (syn_raw lv) ((tw_syn lv).pi_small (syn_raw lv) (syn_raw lv)))
      (LevelTower.IsUniverse.sort _)) ta) tb

theorem syn_rif_typed {c a b : Tm Tower.Head m} (tc : Typed (synStage lv) Δ c rawC)
    (ta : Typed (synStage lv) Δ a rawC) (tb : Typed (synStage lv) Δ b rawC) :
    Typed (synStage lv) Δ (rifC c a b) rawC :=
  .appElim (A := rawC) (B := rawC) (.appElim (A := rawC) (B := .pi rawC rawC)
    (.appElim (A := rawC) (B := .pi rawC (.pi rawC rawC))
      (.const (type := .pi rawC (.pi rawC (.pi rawC rawC))) rfl
        ((tw_syn lv).pi_small (syn_raw lv) ((tw_syn lv).pi_small (syn_raw lv)
          ((tw_syn lv).pi_small (syn_raw lv) (syn_raw lv)))) (LevelTower.IsUniverse.sort _)) tc) ta) tb

theorem syn_rzero_typed {a : Tm Tower.Head m} (ta : Typed (synStage lv) Δ a rawC) :
    Typed (synStage lv) Δ (rzeroC a) rawC :=
  .appElim (A := rawC) (B := rawC)
    (.const (type := .pi rawC rawC) rfl ((tw_syn lv).pi_small (syn_raw lv) (syn_raw lv))
      (LevelTower.IsUniverse.sort _)) ta

/-- `at-num Q x t p : Q t` for `x : Q tnum` and `p : is-num t`. -/
theorem syn_atNum_typed {Q x t p : Tm Tower.Head m} (tQ : Typed (synStage lv) Δ Q (.pi tyC U0))
    (tx : Typed (synStage lv) Δ x (.app Q tnumC)) (tt' : Typed (synStage lv) Δ t tyC)
    (tp : Typed (synStage lv) Δ p (isNumC t)) : Typed (synStage lv) Δ (atNumC Q x t p) (.app Q t) := by
  obtain ⟨w, hw, typed⟩ := atType_typed lv (c := tnum) (f := isNum) rfl rfl
  have tc : Typed (synStage lv) Δ (.const atNum) (liftClosed atNumType) :=
    .const rfl (Derivable.mono (restrict_mono lv (by decide)) typed) hw
  have m₀ : SubstMor (synStage lv) .nil Δ fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (synStage lv) (ofEntries atNumEntries 4) Δ
      (consSub p (consSub t (consSub x (consSub Q fun i => Fin.elim0 i)))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tQ) tx) tt') tp
  exact Typed.telescope_apply mor tc

/-- `at-bool Q x t p : Q t` for `x : Q tbool` and `p : is-bool t`. -/
theorem syn_atBool_typed {Q x t p : Tm Tower.Head m} (tQ : Typed (synStage lv) Δ Q (.pi tyC U0))
    (tx : Typed (synStage lv) Δ x (.app Q tboolC)) (tt' : Typed (synStage lv) Δ t tyC)
    (tp : Typed (synStage lv) Δ p (isBoolC t)) : Typed (synStage lv) Δ (atBoolC Q x t p) (.app Q t) := by
  obtain ⟨w, hw, typed⟩ := atType_typed lv (c := tbool) (f := isBool) rfl rfl
  have tc : Typed (synStage lv) Δ (.const atBool) (liftClosed atBoolType) :=
    .const rfl (Derivable.mono (restrict_mono lv (by decide)) typed) hw
  have m₀ : SubstMor (synStage lv) .nil Δ fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (synStage lv) (ofEntries atBoolEntries 4) Δ
      (consSub p (consSub t (consSub x (consSub Q fun i => Fin.elim0 i)))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tQ) tx) tt') tp
  exact Typed.telescope_apply mor tc

end SynTyping

/-! ### The telescope of the recursion principle -/

/-- The prefix: the family and the five methods. -/
abbrev synCtx : Ctx Tower.Head 6 := ofEntries synEntries 6

theorem synEntry1_typed : Typed (synStage lv) (ofEntries synEntries 1) (synEntries 1) U0 := by
  have tQ : Typed (synStage lv) (.snoc (ofEntries synEntries 1) numC) (.var 1) (.pi tyC U0) := .var 1
  exact (tw_syn lv).pi_small (syn_num lv) (.appElim (A := tyC) (B := U0) tQ (syn_tnum lv))

theorem synEntry2_typed : Typed (synStage lv) (ofEntries synEntries 2) (synEntries 2) U0 := by
  have tQ : Typed (synStage lv) (.snoc (ofEntries synEntries 2) boolC) (.var 2) (.pi tyC U0) := .var 2
  exact (tw_syn lv).pi_small (syn_bool lv) (.appElim (A := tyC) (B := U0) tQ (syn_tbool lv))

theorem synEntry3_typed : Typed (synStage lv) (ofEntries synEntries 3) (synEntries 3) U0 := by
  let Γ : Ctx Tower.Head 3 := ofEntries synEntries 3
  have tQ₀ : Typed (synStage lv) Γ (.var 2) (.pi tyC U0) := .var 2
  have tQ₁ : Typed (synStage lv) (.snoc Γ (.app (.var 2) tnumC)) (.var 3) (.pi tyC U0) := .var 3
  have tQ₂ : Typed (synStage lv) (.snoc (.snoc Γ (.app (.var 2) tnumC)) (.app (.var 3) tnumC)) (.var 4)
      (.pi tyC U0) := .var 4
  exact (tw_syn lv).pi_small (.appElim (A := tyC) (B := U0) tQ₀ (syn_tnum lv))
    ((tw_syn lv).pi_small (.appElim (A := tyC) (B := U0) tQ₁ (syn_tnum lv))
      (.appElim (A := tyC) (B := U0) tQ₂ (syn_tnum lv)))

theorem synEntry4_typed : Typed (synStage lv) (ofEntries synEntries 4) (synEntries 4) U0 := by
  let Γ : Ctx Tower.Head 5 := .snoc (ofEntries synEntries 4) tyC
  have tQ₅ : Typed (synStage lv) Γ (.var 4) (.pi tyC U0) := .var 4
  let Γ₆ : Ctx Tower.Head 6 := .snoc Γ (.app (.var 4) tboolC)
  have tQ₆ : Typed (synStage lv) Γ₆ (.var 5) (.pi tyC U0) := .var 5
  have tt₆ : Typed (synStage lv) Γ₆ (.var 1) tyC := .var 1
  let Γ₇ : Ctx Tower.Head 7 := .snoc Γ₆ (.app (.var 5) (.var 1))
  have tQ₇ : Typed (synStage lv) Γ₇ (.var 6) (.pi tyC U0) := .var 6
  have tt₇ : Typed (synStage lv) Γ₇ (.var 2) tyC := .var 2
  let Γ₈ : Ctx Tower.Head 8 := .snoc Γ₇ (.app (.var 6) (.var 2))
  have tQ₈ : Typed (synStage lv) Γ₈ (.var 7) (.pi tyC U0) := .var 7
  have tt₈ : Typed (synStage lv) Γ₈ (.var 3) tyC := .var 3
  exact (tw_syn lv).pi_small (syn_ty lv)
    ((tw_syn lv).pi_small (.appElim (A := tyC) (B := U0) tQ₅ (syn_tbool lv))
      ((tw_syn lv).pi_small (.appElim (A := tyC) (B := U0) tQ₆ tt₆)
        ((tw_syn lv).pi_small (.appElim (A := tyC) (B := U0) tQ₇ tt₇)
          (.appElim (A := tyC) (B := U0) tQ₈ tt₈))))

theorem synEntry5_typed : Typed (synStage lv) (ofEntries synEntries 5) (synEntries 5) U0 := by
  have tQ₀ : Typed (synStage lv) (ofEntries synEntries 5) (.var 4) (.pi tyC U0) := .var 4
  have tQ₁ : Typed (synStage lv) (.snoc (ofEntries synEntries 5) (.app (.var 4) tnumC)) (.var 5)
      (.pi tyC U0) := .var 5
  exact (tw_syn lv).pi_small (.appElim (A := tyC) (B := U0) tQ₀ (syn_tnum lv))
    (.appElim (A := tyC) (B := U0) tQ₁ (syn_tbool lv))

theorem synCtx_formed : CtxFormed (synStage lv) synCtx :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, tyFamily_typed (tw_syn lv) rfl⟩)
    ⟨_, LevelTower.IsUniverse.sort _, synEntry1_typed lv⟩) ⟨_, LevelTower.IsUniverse.sort _, synEntry2_typed lv⟩)
    ⟨_, LevelTower.IsUniverse.sort _, synEntry3_typed lv⟩) ⟨_, LevelTower.IsUniverse.sort _, synEntry4_typed lv⟩)
    ⟨_, LevelTower.IsUniverse.sort _, synEntry5_typed lv⟩

/-- **The declared type of the recursion principle is typed.** -/
theorem synType_typed : ∃ w, (rules lv).isUniverse w ∧ Typed (synStage lv) .nil synType (.head w) := by
  have tw := tw_syn lv
  let Γ₈ : Ctx Tower.Head 8 := .snoc (.snoc synCtx rawC) tyC
  have tr₈ : Typed (synStage lv) Γ₈ (.var 1) rawC := .var 1
  have tt₈ : Typed (synStage lv) Γ₈ (.var 0) tyC := .var 0
  have e₈ : Typed (synStage lv) Γ₈ (typingC (.var 1) (.var 0)) U0 := syn_typing_typed lv tr₈ tt₈
  have tQ₉ : Typed (synStage lv) (.snoc Γ₈ (typingC (.var 1) (.var 0))) (.var 8) (.pi tyC U0) := .var 8
  have tt₉ : Typed (synStage lv) (.snoc Γ₈ (typingC (.var 1) (.var 0))) (.var 1) tyC := .var 1
  have result : Typed (synStage lv) (.snoc Γ₈ (typingC (.var 1) (.var 0))) (.app (.var 8) (.var 1)) U0 :=
    .appElim (A := tyC) (B := U0) tQ₉ tt₉
  have t₈ := tw.pi_small e₈ result
  have t₇ := tw.pi_small (syn_ty lv) t₈
  have t₆ := tw.pi_small (syn_raw lv) t₇
  have t₅ := tw.pi_small (synEntry5_typed lv) t₆
  have t₄ := tw.pi_small (synEntry4_typed lv) t₅
  have t₃ := tw.pi_small (synEntry3_typed lv) t₄
  have t₂ := tw.pi_small (synEntry2_typed lv) t₃
  have t₁ := tw.pi_small (synEntry1_typed lv) t₂
  exact ⟨_, tw.isUniverse _, .piForm (tyFamily_typed tw rfl) (tw.isUniverse _) t₁ (tw.isUniverse _)
    (tw.join _ _)⟩

/-! ### The equations' contexts -/

/-- The hypothesis type for a recursive field (the field's variable under one binder), with the
family `Q` (its variable under two binders): `Π (t : ty). typed field t → Q t`. -/
abbrev hypType {n : Nat} (field : Fin (n + 1)) (q : Fin (n + 2)) : Tm Tower.Head n :=
  .pi tyC (.pi (typingC (.var field) (.var 0)) (.app (.var q) (.var 1)))

/-! The equations' contexts, over an abstract prefix `Γ` of the family and the five methods; the
equations' own contexts are these at the telescope's prefix `synCtx`. -/

abbrev numCtxOf (Γ : Ctx Tower.Head 6) : Ctx Tower.Head 9 :=
  .snoc (.snoc (.snoc Γ numC) tyC) (typingC (rnumC (.var 1)) (.var 0))
abbrev boolCtxOf (Γ : Ctx Tower.Head 6) : Ctx Tower.Head 9 :=
  .snoc (.snoc (.snoc Γ boolC) tyC) (typingC (rboolC (.var 1)) (.var 0))
abbrev addCtxOf (Γ : Ctx Tower.Head 6) : Ctx Tower.Head 12 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) tyC) (typingC (raddC (.var 2) (.var 1)) (.var 0)))
    (hypType (n := 10) 4 11)) (hypType (n := 11) 4 12)
abbrev ifCtxOf (Γ : Ctx Tower.Head 6) : Ctx Tower.Head 14 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) tyC)
    (typingC (rifC (.var 3) (.var 2) (.var 1)) (.var 0))) (hypType (n := 11) 5 12)) (hypType (n := 12) 5 13))
    (hypType (n := 13) 5 14)
abbrev zeroCtxOf (Γ : Ctx Tower.Head 6) : Ctx Tower.Head 10 :=
  .snoc (.snoc (.snoc (.snoc Γ rawC) tyC) (typingC (rzeroC (.var 1)) (.var 0))) (hypType (n := 9) 3 10)

abbrev numCtx : Ctx Tower.Head 9 := numCtxOf synCtx
abbrev boolCtx : Ctx Tower.Head 9 := boolCtxOf synCtx
abbrev addCtx : Ctx Tower.Head 12 := addCtxOf synCtx
abbrev ifCtx : Ctx Tower.Head 14 := ifCtxOf synCtx
abbrev zeroCtx : Ctx Tower.Head 10 := zeroCtxOf synCtx

/-- The family `Q` and the methods at the prefix, as typings of its variables. -/
structure Prefix (Γ : Ctx Tower.Head 6) : Prop where
  formed : CtxFormed (synStage lv) Γ
  hQ : Typed (synStage lv) Γ (.var 5) (.pi tyC U0)
  hm₁ : Typed (synStage lv) Γ (.var 4) (.pi numC (.app (.var 6) tnumC))
  hm₂ : Typed (synStage lv) Γ (.var 3) (.pi boolC (.app (.var 6) tboolC))
  hm₃ : Typed (synStage lv) Γ (.var 2) (.pi (.app (.var 5) tnumC) (.pi (.app (.var 6) tnumC) (.app (.var 7) tnumC)))
  hm₄ : Typed (synStage lv) Γ (.var 1)
    (.pi tyC (.pi (.app (.var 6) tboolC) (.pi (.app (.var 7) (.var 1)) (.pi (.app (.var 8) (.var 2))
      (.app (.var 9) (.var 3))))))
  hm₅ : Typed (synStage lv) Γ (.var 0) (.pi (.app (.var 5) tnumC) (.app (.var 6) tboolC))

/-- A hypothesis type is a small type where its field is an expression and its family is `Q`. -/
theorem hypType_typed {n : Nat} {Γ : Ctx Tower.Head n} (field : Fin (n + 1)) (q : Fin (n + 2))
    (tField : Typed (synStage lv) (.snoc Γ tyC) (.var field) rawC)
    (tQ : Typed (synStage lv) (.snoc (.snoc Γ tyC) (typingC (.var field) (.var 0))) (.var q) (.pi tyC U0)) :
    Typed (synStage lv) Γ (hypType field q) U0 := by
  have tt₁ : Typed (synStage lv) (.snoc Γ tyC) (.var 0) tyC := .var 0
  have tt₂ : Typed (synStage lv) (.snoc (.snoc Γ tyC) (typingC (.var field) (.var 0))) (.var 1) tyC := .var 1
  exact (tw_syn lv).pi_small (syn_ty lv) ((tw_syn lv).pi_small (syn_typing_typed lv tField tt₁)
    (.appElim (A := tyC) (B := U0) tQ tt₂))

section PrefixFormed

variable {Γ : Ctx Tower.Head 6} (P : Prefix lv Γ)
include P

theorem numCtx_formed_of : CtxFormed (synStage lv) (numCtxOf Γ) := by
  have tk : Typed (synStage lv) (.snoc (.snoc Γ numC) tyC) (.var 1) numC := .var 1
  have tt' : Typed (synStage lv) (.snoc (.snoc Γ numC) tyC) (.var 0) tyC := .var 0
  exact .snoc (.snoc (.snoc P.formed ⟨_, LevelTower.IsUniverse.sort _, syn_num lv⟩)
    ⟨_, LevelTower.IsUniverse.sort _, syn_ty lv⟩)
    ⟨_, LevelTower.IsUniverse.sort _, syn_typing_typed lv (syn_rnum_typed lv tk) tt'⟩

theorem boolCtx_formed_of : CtxFormed (synStage lv) (boolCtxOf Γ) := by
  have tb : Typed (synStage lv) (.snoc (.snoc Γ boolC) tyC) (.var 1) boolC := .var 1
  have tt' : Typed (synStage lv) (.snoc (.snoc Γ boolC) tyC) (.var 0) tyC := .var 0
  exact .snoc (.snoc (.snoc P.formed ⟨_, LevelTower.IsUniverse.sort _, syn_bool lv⟩)
    ⟨_, LevelTower.IsUniverse.sort _, syn_ty lv⟩)
    ⟨_, LevelTower.IsUniverse.sort _, syn_typing_typed lv (syn_rbool_typed lv tb) tt'⟩

theorem addCtx_formed_of : CtxFormed (synStage lv) (addCtxOf Γ) := by
  have ta : Typed (synStage lv) (.snoc (.snoc (.snoc Γ rawC) rawC) tyC) (.var 2) rawC := .var 2
  have tb : Typed (synStage lv) (.snoc (.snoc (.snoc Γ rawC) rawC) tyC) (.var 1) rawC := .var 1
  have tt' : Typed (synStage lv) (.snoc (.snoc (.snoc Γ rawC) rawC) tyC) (.var 0) tyC := .var 0
  have tA : Typed (synStage lv) (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) tyC)
      (typingC (raddC (.var 2) (.var 1)) (.var 0))) (hypType (n := 10) 4 11) U0 :=
    hypType_typed lv 4 11 (.var 4) P.hQ.weaken.weaken.weaken.weaken.weaken.weaken
  have tB : Typed (synStage lv) (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) tyC)
      (typingC (raddC (.var 2) (.var 1)) (.var 0))) (hypType (n := 10) 4 11)) (hypType (n := 11) 4 12) U0 :=
    hypType_typed lv 4 12 (.var 4) P.hQ.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  exact .snoc (.snoc (.snoc (.snoc (.snoc (.snoc P.formed ⟨_, LevelTower.IsUniverse.sort _, syn_raw lv⟩)
    ⟨_, LevelTower.IsUniverse.sort _, syn_raw lv⟩) ⟨_, LevelTower.IsUniverse.sort _, syn_ty lv⟩)
    ⟨_, LevelTower.IsUniverse.sort _, syn_typing_typed lv (syn_radd_typed lv ta tb) tt'⟩)
    ⟨_, LevelTower.IsUniverse.sort _, tA⟩) ⟨_, LevelTower.IsUniverse.sort _, tB⟩

theorem ifCtx_formed_of : CtxFormed (synStage lv) (ifCtxOf Γ) := by
  have tc : Typed (synStage lv) (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) tyC) (.var 3) rawC := .var 3
  have ta : Typed (synStage lv) (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) tyC) (.var 2) rawC := .var 2
  have tb : Typed (synStage lv) (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) tyC) (.var 1) rawC := .var 1
  have tt' : Typed (synStage lv) (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) tyC) (.var 0) tyC := .var 0
  have tC : Typed (synStage lv) (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) tyC)
      (typingC (rifC (.var 3) (.var 2) (.var 1)) (.var 0))) (hypType (n := 11) 5 12) U0 :=
    hypType_typed lv 5 12 (.var 5) P.hQ.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  have tA : Typed (synStage lv) (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) tyC)
      (typingC (rifC (.var 3) (.var 2) (.var 1)) (.var 0))) (hypType (n := 11) 5 12))
      (hypType (n := 12) 5 13) U0 :=
    hypType_typed lv 5 13 (.var 5) P.hQ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  have tB : Typed (synStage lv) (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) tyC)
      (typingC (rifC (.var 3) (.var 2) (.var 1)) (.var 0))) (hypType (n := 11) 5 12)) (hypType (n := 12) 5 13))
      (hypType (n := 13) 5 14) U0 :=
    hypType_typed lv 5 14 (.var 5) P.hQ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  exact .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc P.formed
    ⟨_, LevelTower.IsUniverse.sort _, syn_raw lv⟩) ⟨_, LevelTower.IsUniverse.sort _, syn_raw lv⟩)
    ⟨_, LevelTower.IsUniverse.sort _, syn_raw lv⟩) ⟨_, LevelTower.IsUniverse.sort _, syn_ty lv⟩)
    ⟨_, LevelTower.IsUniverse.sort _, syn_typing_typed lv (syn_rif_typed lv tc ta tb) tt'⟩)
    ⟨_, LevelTower.IsUniverse.sort _, tC⟩) ⟨_, LevelTower.IsUniverse.sort _, tA⟩)
    ⟨_, LevelTower.IsUniverse.sort _, tB⟩

theorem zeroCtx_formed_of : CtxFormed (synStage lv) (zeroCtxOf Γ) := by
  have ta : Typed (synStage lv) (.snoc (.snoc Γ rawC) tyC) (.var 1) rawC := .var 1
  have tt' : Typed (synStage lv) (.snoc (.snoc Γ rawC) tyC) (.var 0) tyC := .var 0
  have tA : Typed (synStage lv) (.snoc (.snoc (.snoc Γ rawC) tyC) (typingC (rzeroC (.var 1)) (.var 0)))
      (hypType (n := 9) 3 10) U0 :=
    hypType_typed lv 3 10 (.var 3) P.hQ.weaken.weaken.weaken.weaken.weaken
  exact .snoc (.snoc (.snoc (.snoc P.formed ⟨_, LevelTower.IsUniverse.sort _, syn_raw lv⟩)
    ⟨_, LevelTower.IsUniverse.sort _, syn_ty lv⟩)
    ⟨_, LevelTower.IsUniverse.sort _, syn_typing_typed lv (syn_rzero_typed lv ta) tt'⟩)
    ⟨_, LevelTower.IsUniverse.sort _, tA⟩

end PrefixFormed

/-- The telescope's prefix: the family and the five methods. -/
theorem synPrefix : Prefix lv synCtx where
  formed := synCtx_formed lv
  hQ := .var 5
  hm₁ := .var 4
  hm₂ := .var 3
  hm₃ := .var 2
  hm₄ := .var 1
  hm₅ := .var 0

theorem numCtx_formed : CtxFormed (synStage lv) numCtx := numCtx_formed_of lv (synPrefix lv)
theorem boolCtx_formed : CtxFormed (synStage lv) boolCtx := boolCtx_formed_of lv (synPrefix lv)
theorem addCtx_formed : CtxFormed (synStage lv) addCtx := addCtx_formed_of lv (synPrefix lv)
theorem ifCtx_formed : CtxFormed (synStage lv) ifCtx := ifCtx_formed_of lv (synPrefix lv)
theorem zeroCtx_formed : CtxFormed (synStage lv) zeroCtx := zeroCtx_formed_of lv (synPrefix lv)

/-! ### The right-hand sides are typed -/

section PrefixBodies

variable {Γ : Ctx Tower.Head 6} (P : Prefix lv Γ)
include P

theorem numBody_of :
    Typed (synStage lv) (numCtxOf Γ) (atNumC (.var 8) (.app (.var 7) (.var 2)) (.var 1) (.var 0))
      (.app (.var 8) (.var 1)) := by
  have tQ : Typed (synStage lv) (numCtxOf Γ) (.var 8) (.pi tyC U0) := P.hQ.weaken.weaken.weaken
  have tm : Typed (synStage lv) (numCtxOf Γ) (.var 7) (.pi numC (.app (.var 9) tnumC)) :=
    P.hm₁.weaken.weaken.weaken
  have tk : Typed (synStage lv) (numCtxOf Γ) (.var 2) numC := .var 2
  have tt' : Typed (synStage lv) (numCtxOf Γ) (.var 1) tyC := .var 1
  have tp : Typed (synStage lv) (numCtxOf Γ) (.var 0) (typingC (rnumC (.var 2)) (.var 1)) := .var 0
  have eq : Equal (synStage lv) (numCtxOf Γ) (typingC (rnumC (.var 2)) (.var 1)) (isNumC (.var 1)) U0 :=
    .root (typing_rnum_step lv (.var 2) (.var 1)) (syn_typing_typed lv (syn_rnum_typed lv tk) tt')
      (syn_isNum_typed lv tt')
  exact syn_atNum_typed lv tQ (.appElim tm tk) tt' (Typed.convType tp ⟨_, LevelTower.IsUniverse.sort _, eq⟩)

theorem boolBody_of :
    Typed (synStage lv) (boolCtxOf Γ) (atBoolC (.var 8) (.app (.var 6) (.var 2)) (.var 1) (.var 0))
      (.app (.var 8) (.var 1)) := by
  have tQ : Typed (synStage lv) (boolCtxOf Γ) (.var 8) (.pi tyC U0) := P.hQ.weaken.weaken.weaken
  have tm : Typed (synStage lv) (boolCtxOf Γ) (.var 6) (.pi boolC (.app (.var 9) tboolC)) :=
    P.hm₂.weaken.weaken.weaken
  have tb : Typed (synStage lv) (boolCtxOf Γ) (.var 2) boolC := .var 2
  have tt' : Typed (synStage lv) (boolCtxOf Γ) (.var 1) tyC := .var 1
  have tp : Typed (synStage lv) (boolCtxOf Γ) (.var 0) (typingC (rboolC (.var 2)) (.var 1)) := .var 0
  have eq : Equal (synStage lv) (boolCtxOf Γ) (typingC (rboolC (.var 2)) (.var 1)) (isBoolC (.var 1)) U0 :=
    .root (typing_rbool_step lv (.var 2) (.var 1)) (syn_typing_typed lv (syn_rbool_typed lv tb) tt')
      (syn_isBool_typed lv tt')
  exact syn_atBool_typed lv tQ (.appElim tm tb) tt' (Typed.convType tp ⟨_, LevelTower.IsUniverse.sort _, eq⟩)

theorem addBody_of :
    Typed (synStage lv) (addCtxOf Γ)
      (atNumC (.var 11)
        (.app (.app (.var 8) (.app (.app (.var 1) tnumC) (.fst (.snd (.var 2)))))
          (.app (.app (.var 0) tnumC) (.snd (.snd (.var 2)))))
        (.var 3) (.fst (.var 2)))
      (.app (.var 11) (.var 3)) := by
  have tw := tw_syn lv
  have tQ : Typed (synStage lv) (addCtxOf Γ) (.var 11) (.pi tyC U0) :=
    P.hQ.weaken.weaken.weaken.weaken.weaken.weaken
  have ta : Typed (synStage lv) (addCtxOf Γ) (.var 5) rawC := .var 5
  have tb : Typed (synStage lv) (addCtxOf Γ) (.var 4) rawC := .var 4
  have tt' : Typed (synStage lv) (addCtxOf Γ) (.var 3) tyC := .var 3
  have tp : Typed (synStage lv) (addCtxOf Γ) (.var 2) (typingC (raddC (.var 5) (.var 4)) (.var 3)) := .var 2
  -- the shape of the proof
  have ta₁ : Typed (synStage lv) (.snoc (addCtxOf Γ) (isNumC (.var 3))) (.var 6) rawC := .var 6
  have tb₂ : Typed (synStage lv) (.snoc (.snoc (addCtxOf Γ) (isNumC (.var 3))) (typingC (.var 6) tnumC))
      (.var 6) rawC := .var 6
  have tSigma : Typed (synStage lv) (addCtxOf Γ)
      (.sigma (isNumC (.var 3)) (.sigma (typingC (.var 6) tnumC) (typingC (.var 6) tnumC))) U0 :=
    tw.sigma_small (syn_isNum_typed lv tt')
      (tw.sigma_small (syn_typing_typed lv ta₁ (syn_tnum lv)) (syn_typing_typed lv tb₂ (syn_tnum lv)))
  have eq : Equal (synStage lv) (addCtxOf Γ) (typingC (raddC (.var 5) (.var 4)) (.var 3))
      (.sigma (isNumC (.var 3)) (.sigma (typingC (.var 6) tnumC) (typingC (.var 6) tnumC))) U0 :=
    .root (typing_radd_step lv (.var 5) (.var 4) (.var 3)) (syn_typing_typed lv (syn_radd_typed lv ta tb) tt')
      tSigma
  have tp' := Typed.convType tp ⟨_, LevelTower.IsUniverse.sort _, eq⟩
  have tu : Typed (synStage lv) (addCtxOf Γ) (.fst (.var 2)) (isNumC (.var 3)) := .fstElim tp'
  have tq : Typed (synStage lv) (addCtxOf Γ) (.snd (.var 2))
      (.sigma (typingC (.var 5) tnumC) (typingC (.var 5) tnumC)) := .sndElim tp'
  have tq₁ : Typed (synStage lv) (addCtxOf Γ) (.fst (.snd (.var 2))) (typingC (.var 5) tnumC) := .fstElim tq
  have tq₂ : Typed (synStage lv) (addCtxOf Γ) (.snd (.snd (.var 2))) (typingC (.var 4) tnumC) := .sndElim tq
  -- the recursive calls at `tnum`
  have tha : Typed (synStage lv) (addCtxOf Γ) (.var 1) (hypType (n := 12) 6 13) := .var 1
  have thb : Typed (synStage lv) (addCtxOf Γ) (.var 0) (hypType (n := 12) 5 13) := .var 0
  have ha : Typed (synStage lv) (addCtxOf Γ) (.app (.app (.var 1) tnumC) (.fst (.snd (.var 2))))
      (.app (.var 11) tnumC) :=
    .appElim (.appElim tha (syn_tnum lv)) tq₁
  have hb : Typed (synStage lv) (addCtxOf Γ) (.app (.app (.var 0) tnumC) (.snd (.snd (.var 2))))
      (.app (.var 11) tnumC) :=
    .appElim (.appElim thb (syn_tnum lv)) tq₂
  have tmadd : Typed (synStage lv) (addCtxOf Γ) (.var 8)
      (.pi (.app (.var 11) tnumC) (.pi (.app (.var 12) tnumC) (.app (.var 13) tnumC))) :=
    P.hm₃.weaken.weaken.weaken.weaken.weaken.weaken
  have tx : Typed (synStage lv) (addCtxOf Γ)
      (.app (.app (.var 8) (.app (.app (.var 1) tnumC) (.fst (.snd (.var 2)))))
        (.app (.app (.var 0) tnumC) (.snd (.snd (.var 2))))) (.app (.var 11) tnumC) :=
    .appElim (.appElim tmadd ha) hb
  exact syn_atNum_typed lv tQ tx tt' tu

theorem ifBody_of :
    Typed (synStage lv) (ifCtxOf Γ)
      (.app (.app (.app (.app (.var 9) (.var 4)) (.app (.app (.var 2) tboolC) (.fst (.var 3))))
        (.app (.app (.var 1) (.var 4)) (.fst (.snd (.var 3)))))
        (.app (.app (.var 0) (.var 4)) (.snd (.snd (.var 3)))))
      (.app (.var 13) (.var 4)) := by
  have tw := tw_syn lv
  have tc : Typed (synStage lv) (ifCtxOf Γ) (.var 7) rawC := .var 7
  have ta : Typed (synStage lv) (ifCtxOf Γ) (.var 6) rawC := .var 6
  have tb : Typed (synStage lv) (ifCtxOf Γ) (.var 5) rawC := .var 5
  have tt' : Typed (synStage lv) (ifCtxOf Γ) (.var 4) tyC := .var 4
  have tp : Typed (synStage lv) (ifCtxOf Γ) (.var 3) (typingC (rifC (.var 7) (.var 6) (.var 5)) (.var 4)) :=
    .var 3
  have ta₁ : Typed (synStage lv) (.snoc (ifCtxOf Γ) (typingC (.var 7) tboolC)) (.var 7) rawC := .var 7
  have tt₁ : Typed (synStage lv) (.snoc (ifCtxOf Γ) (typingC (.var 7) tboolC)) (.var 5) tyC := .var 5
  have tb₂ : Typed (synStage lv) (.snoc (.snoc (ifCtxOf Γ) (typingC (.var 7) tboolC)) (typingC (.var 7) (.var 5)))
      (.var 7) rawC := .var 7
  have tt₂ : Typed (synStage lv) (.snoc (.snoc (ifCtxOf Γ) (typingC (.var 7) tboolC)) (typingC (.var 7) (.var 5)))
      (.var 6) tyC := .var 6
  have tSigma : Typed (synStage lv) (ifCtxOf Γ)
      (.sigma (typingC (.var 7) tboolC) (.sigma (typingC (.var 7) (.var 5)) (typingC (.var 7) (.var 6)))) U0 :=
    tw.sigma_small (syn_typing_typed lv tc (syn_tbool lv))
      (tw.sigma_small (syn_typing_typed lv ta₁ tt₁) (syn_typing_typed lv tb₂ tt₂))
  have eq : Equal (synStage lv) (ifCtxOf Γ) (typingC (rifC (.var 7) (.var 6) (.var 5)) (.var 4))
      (.sigma (typingC (.var 7) tboolC) (.sigma (typingC (.var 7) (.var 5)) (typingC (.var 7) (.var 6)))) U0 :=
    .root (typing_rif_step lv (.var 7) (.var 6) (.var 5) (.var 4))
      (syn_typing_typed lv (syn_rif_typed lv tc ta tb) tt') tSigma
  have tp' := Typed.convType tp ⟨_, LevelTower.IsUniverse.sort _, eq⟩
  have tqc : Typed (synStage lv) (ifCtxOf Γ) (.fst (.var 3)) (typingC (.var 7) tboolC) := .fstElim tp'
  have tq : Typed (synStage lv) (ifCtxOf Γ) (.snd (.var 3))
      (.sigma (typingC (.var 6) (.var 4)) (typingC (.var 6) (.var 5))) := .sndElim tp'
  have tqa : Typed (synStage lv) (ifCtxOf Γ) (.fst (.snd (.var 3))) (typingC (.var 6) (.var 4)) := .fstElim tq
  have tqb : Typed (synStage lv) (ifCtxOf Γ) (.snd (.snd (.var 3))) (typingC (.var 5) (.var 4)) := .sndElim tq
  have thc : Typed (synStage lv) (ifCtxOf Γ) (.var 2) (hypType (n := 14) 8 15) := .var 2
  have tha : Typed (synStage lv) (ifCtxOf Γ) (.var 1) (hypType (n := 14) 7 15) := .var 1
  have thb : Typed (synStage lv) (ifCtxOf Γ) (.var 0) (hypType (n := 14) 6 15) := .var 0
  have hc : Typed (synStage lv) (ifCtxOf Γ) (.app (.app (.var 2) tboolC) (.fst (.var 3))) (.app (.var 13) tboolC) :=
    .appElim (.appElim thc (syn_tbool lv)) tqc
  have ha : Typed (synStage lv) (ifCtxOf Γ) (.app (.app (.var 1) (.var 4)) (.fst (.snd (.var 3))))
      (.app (.var 13) (.var 4)) :=
    .appElim (.appElim tha tt') tqa
  have hb : Typed (synStage lv) (ifCtxOf Γ) (.app (.app (.var 0) (.var 4)) (.snd (.snd (.var 3))))
      (.app (.var 13) (.var 4)) :=
    .appElim (.appElim thb tt') tqb
  have tmif : Typed (synStage lv) (ifCtxOf Γ) (.var 9)
      (.pi tyC (.pi (.app (.var 14) tboolC) (.pi (.app (.var 15) (.var 1))
        (.pi (.app (.var 16) (.var 2)) (.app (.var 17) (.var 3)))))) :=
    P.hm₄.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  exact .appElim (.appElim (.appElim (.appElim tmif tt') hc) ha) hb

theorem zeroBody_of :
    Typed (synStage lv) (zeroCtxOf Γ)
      (atBoolC (.var 9) (.app (.var 4) (.app (.app (.var 0) tnumC) (.snd (.var 1)))) (.var 2) (.fst (.var 1)))
      (.app (.var 9) (.var 2)) := by
  have tw := tw_syn lv
  have tQ : Typed (synStage lv) (zeroCtxOf Γ) (.var 9) (.pi tyC U0) := P.hQ.weaken.weaken.weaken.weaken
  have ta : Typed (synStage lv) (zeroCtxOf Γ) (.var 3) rawC := .var 3
  have tt' : Typed (synStage lv) (zeroCtxOf Γ) (.var 2) tyC := .var 2
  have tp : Typed (synStage lv) (zeroCtxOf Γ) (.var 1) (typingC (rzeroC (.var 3)) (.var 2)) := .var 1
  have ta₁ : Typed (synStage lv) (.snoc (zeroCtxOf Γ) (isBoolC (.var 2))) (.var 4) rawC := .var 4
  have tSigma : Typed (synStage lv) (zeroCtxOf Γ) (.sigma (isBoolC (.var 2)) (typingC (.var 4) tnumC)) U0 :=
    tw.sigma_small (syn_isBool_typed lv tt') (syn_typing_typed lv ta₁ (syn_tnum lv))
  have eq : Equal (synStage lv) (zeroCtxOf Γ) (typingC (rzeroC (.var 3)) (.var 2))
      (.sigma (isBoolC (.var 2)) (typingC (.var 4) tnumC)) U0 :=
    .root (typing_rzero_step lv (.var 3) (.var 2)) (syn_typing_typed lv (syn_rzero_typed lv ta) tt') tSigma
  have tp' := Typed.convType tp ⟨_, LevelTower.IsUniverse.sort _, eq⟩
  have tu : Typed (synStage lv) (zeroCtxOf Γ) (.fst (.var 1)) (isBoolC (.var 2)) := .fstElim tp'
  have tq : Typed (synStage lv) (zeroCtxOf Γ) (.snd (.var 1)) (typingC (.var 3) tnumC) := .sndElim tp'
  have tha : Typed (synStage lv) (zeroCtxOf Γ) (.var 0) (hypType (n := 10) 4 11) := .var 0
  have ha : Typed (synStage lv) (zeroCtxOf Γ) (.app (.app (.var 0) tnumC) (.snd (.var 1))) (.app (.var 9) tnumC) :=
    .appElim (.appElim tha (syn_tnum lv)) tq
  have tmzero : Typed (synStage lv) (zeroCtxOf Γ) (.var 4) (.pi (.app (.var 9) tnumC) (.app (.var 10) tboolC)) :=
    P.hm₅.weaken.weaken.weaken.weaken
  exact syn_atBool_typed lv tQ (.appElim tmzero ha) tt' tu

end PrefixBodies

section Declarations

variable (valuation : Nat → Nat) {E : GenericEquality Tower.Head} (lawsE : E.Laws (rules lv) roles)
include lawsE

/-- **The package declares the recursion principle of typed expressions**, by structural recursion on
the untyped expression. -/
theorem declaresSynRec :
    DeclaresRecursion (settingAt lv valuation E) (synStage lv) synRec raw rawCtors synEntries 6 2 synResult
      synBody where
  role := roles_synRec
  scrutinee := rfl
  declared := rfl
  sub₀ := sub_restrict lv _ (by decide)
  semantic₀ := semantic_syn lv valuation lawsE
  typed := synType_typed lv
  formed := by
    intro k fields mem
    simp only [rawCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact numCtx_formed lv
    · exact boolCtx_formed lv
    · exact addCtx_formed lv
    · exact ifCtx_formed lv
    · exact zeroCtx_formed lv
  bodyTyped := by
    intro k fields mem
    simp only [rawCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact numBody_of lv (synPrefix lv)
    · exact boolBody_of lv (synPrefix lv)
    · exact addBody_of lv (synPrefix lv)
    · exact ifBody_of lv (synPrefix lv)
    · exact zeroBody_of lv (synPrefix lv)
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll mem_synRec ⟨_, _, σ, as, mem, has, rfl, rfl⟩

/-- **Every declared constant is semantic**, for any generic equality with the laws. -/
theorem semantic_all : AllSemantic (settingAt lv valuation E) (restrict lv allNames) := by
  refine allSemantic_restrict lv fun name mem type declared => ?_
  simp only [allNames, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> cases declared
  · exact (declaresNum lv valuation).type_semantic lawsE
  · exact (declaresNum lv valuation).ctor_semantic lawsE mem_zero
  · exact (declaresNum lv valuation).ctor_semantic lawsE mem_succ
  · exact (declaresNum lv valuation).rec_semantic lawsE
  · exact (declaresUnit lv valuation).type_semantic lawsE
  · exact (declaresUnit lv valuation).ctor_semantic lawsE TowerVectorsModel.mem_tt
  · exact (declaresUnit lv valuation).rec_semantic lawsE
  · exact (declaresVoid lv valuation).type_semantic lawsE
  · exact (declaresVoid lv valuation).rec_semantic lawsE
  · exact (declaresBool lv valuation).type_semantic lawsE
  · exact (declaresBool lv valuation).ctor_semantic lawsE mem_btrue
  · exact (declaresBool lv valuation).ctor_semantic lawsE mem_bfalse
  · exact (declaresBool lv valuation).rec_semantic lawsE
  · exact (declaresTy lv valuation).type_semantic lawsE
  · exact (declaresTy lv valuation).ctor_semantic lawsE mem_tnum
  · exact (declaresTy lv valuation).ctor_semantic lawsE mem_tbool
  · exact (declaresTy lv valuation).rec_semantic lawsE
  · exact (declaresRaw lv valuation lawsE).type_semantic lawsE
  · exact (declaresRaw lv valuation lawsE).ctor_semantic lawsE mem_rnum
  · exact (declaresRaw lv valuation lawsE).ctor_semantic lawsE mem_rbool
  · exact (declaresRaw lv valuation lawsE).ctor_semantic lawsE mem_radd
  · exact (declaresRaw lv valuation lawsE).ctor_semantic lawsE mem_rif
  · exact (declaresRaw lv valuation lawsE).ctor_semantic lawsE mem_rzero
  · exact (declaresRaw lv valuation lawsE).rec_semantic lawsE
  · intro m Δ formed P r
    exact (declaresAdd lv valuation lawsE).semantic lawsE (declaresNum lv valuation) formed r
  · intro m Δ formed P r
    exact (declaresIsZero lv valuation lawsE).semantic lawsE (declaresNum lv valuation) formed r
  · intro m Δ formed P r
    exact (declaresIsNum lv valuation lawsE).semantic lawsE (declaresTy lv valuation) formed r
  · intro m Δ formed P r
    exact (declaresIsBool lv valuation lawsE).semantic lawsE (declaresTy lv valuation) formed r
  · intro m Δ formed P r
    exact (declaresVal lv valuation lawsE).semantic lawsE (declaresTy lv valuation) formed r
  · intro m Δ formed P r
    exact (declaresTyping lv valuation lawsE).semantic lawsE (declaresRaw lv valuation lawsE) formed r
  · intro m Δ formed P r
    exact (declaresAtNum lv valuation lawsE).semantic lawsE (declaresTy lv valuation) formed r
  · intro m Δ formed P r
    exact (declaresAtBool lv valuation lawsE).semantic lawsE (declaresTy lv valuation) formed r
  · intro m Δ formed P r
    exact (declaresSynRec lv valuation lawsE).semantic lawsE (declaresRaw lv valuation lawsE) formed r

/-- **Every declared constant is semantic**, at every generic equality with the laws, so for the typed
equality and for the algorithmic equality alike. -/
theorem constantsAt : SemanticConstants (settingAt lv valuation E) :=
  AllSemantic.semanticConstantsOf (semantic_all lv valuation lawsE)

end Declarations

/-- **Every declared constant is semantic**, for the typed equality. -/
theorem constants (valuation : Nat → Nat) : SemanticConstants (setting lv valuation) :=
  constantsAt lv valuation (laws lv valuation)

/-! ## The hypotheses of the model -/

/-- **The facts about the weak-head forms of the package's types.** -/
theorem facts : FormFacts (rules lv) roles :=
  .ofSemantic (S := setting lv fun _ => 0) (laws lv _) (constants lv _)

/-- **Every equation preserves typing**: the six recursors and the nine definitions. -/
theorem roots : RootPreserving (rules lv) := by
  intro n Γ l r A formed step typing
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (declaresNum lv (fun _ => 0) (E := declarative (rules lv))).toRecursor.step_preserves
      (facts lv) (RulesSub.refl _) formed h typing
  · exact (declaresUnit lv (fun _ => 0) (E := declarative (rules lv))).toRecursor.step_preserves
      (facts lv) (RulesSub.refl _) formed h typing
  · exact (declaresVoid lv (fun _ => 0) (E := declarative (rules lv))).toRecursor.step_preserves
      (facts lv) (RulesSub.refl _) formed h typing
  · exact (declaresBool lv (fun _ => 0) (E := declarative (rules lv))).toRecursor.step_preserves
      (facts lv) (RulesSub.refl _) formed h typing
  · exact (declaresTy lv (fun _ => 0) (E := declarative (rules lv))).toRecursor.step_preserves
      (facts lv) (RulesSub.refl _) formed h typing
  · exact (declaresRaw lv (fun _ => 0) (laws lv fun _ => 0)).toRecursor.step_preserves
      (facts lv) (RulesSub.refl _) formed h typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresAdd lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresNum lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresIsZero lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresNum lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresIsNum lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresTy lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresIsBool lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresTy lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresVal lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresTy lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresTyping lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresRaw lv (fun _ => 0) (laws lv fun _ => 0)) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresAtNum lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresTy lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresAtBool lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresTy lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresSynRec lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresRaw lv (fun _ => 0) (laws lv fun _ => 0)) (RulesSub.refl _) formed mem σ as has typing

/-- Head equality steps preserve typing. -/
theorem heads : HeadPreserving (rules lv) := by
  intro n Γ h h' A same typing
  obtain ⟨w, headTyping, le⟩ := Typed.generation typing
  cases headTyping with
  | legacyGround =>
      cases h' with
      | legacyGround => exact Typed.subsume (.headType .legacyGround) le
      | sort _ => exact same.elim
  | sort l =>
      cases h' with
      | legacyGround => exact same.elim
      | sort r =>
          have raise : (rules lv).cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show LevelExpr.eval ν r + 1 ≤ LevelExpr.eval ν l + 1
            have := same ν
            omega
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

theorem algebra : CumulativeAlgebra (rules lv) where
  trans := TowerModel.algebra.trans
  same_left := TowerModel.algebra.same_left
  same_right := TowerModel.algebra.same_right
  join_least := TowerModel.algebra.join_least

end TowerSyntaxModel

#print axioms TowerSyntaxModel.declaresAtNum
#print axioms TowerSyntaxModel.declaresAtBool
#print axioms TowerSyntaxModel.declaresSynRec
#print axioms TowerSyntaxModel.semantic_all
#print axioms TowerSyntaxModel.constantsAt
#print axioms TowerSyntaxModel.constants
#print axioms TowerSyntaxModel.facts
#print axioms TowerSyntaxModel.roots
#print axioms TowerSyntaxModel.heads
#print axioms TowerSyntaxModel.algebra

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
