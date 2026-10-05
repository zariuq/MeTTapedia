import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConvConstants
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueRecursor

/-!
# The recursor on the numbers in the conversion model

The recursor `num-rec P z s n` computes at `zero` to `z`, and at `suc m` to
`s m (num-rec P z s m)`, on the value side of the model and on the realizer side
alike. It is a valid term of its declared type
`Π P : num → U₀. P zero → (Π n : num. P n → P (suc n)) → Π n : num. P n`
(`valid_numRec`):

* **Values**, by induction on the common shape of two related numbers: at zero
  both sides compute to the values at zero, at a successor to the steps applied
  to the predecessors and to the recursive calls, related by induction, and at
  the daimon both are stuck on it (`numRec_related`).
* **Realizers**, by induction on the shape of the number, read from the
  realizers of the number (`numRec_real`): realizers reaching neutral terms make
  both applications reach neutral spines, which the generic equality compares
  argument by argument; realizers reaching `zero` make both applications
  compute to the realizers of the value at zero; realizers reaching `suc` make
  both compute to the step's realizers applied to the predecessor's realizers
  and to the recursive calls, which the step's realizers send to realizers of
  the step's value. The realizer types are converted along the typed equalities
  that the reductions carry.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization hiding World
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Conversion
open Presentation.TypedEquality.Impredicative.Consistency (World Morph)
open Presentation.TypedEquality.Impredicative.Realizability (HasShape)
open StrongNormalization (NumShape)
open TelescopeAbstraction (closeType applyClosed)
open SetProfile (zeroNative sucNative)
open Package (U0 numT numRecName numRecType numRecApp numRecTelescope)

namespace CodeModel
namespace ConvRules

/-! ## The recursor on the realizer side -/

/-- The recursor at its declared type in the executable package. -/
theorem rules_numRec_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed rules Γ (.const numRecName) (liftClosed numRecType) := by
  have declared : rules.constantType numRecName = some numRecType := by decide
  exact .const declared (Derivable.mono (stage_sub_rules _) numRecType_typed) (LevelTower.IsUniverse.sort _)

/-- The substitution of the recursor's telescope by a motive, a value at zero and
a step. -/
def recArgs {n : Nat} (p z s : Tower.Tm n) : Sub Tower.Head 3 n :=
  consSub s (consSub z (consSub p fun i => Fin.elim0 i))

section Typings

variable {T : RealizerSide Tower.Head ℕ} (ext : OverRules T) {n : Nat} {Δ : Tower.Ctx n}
  {p z s : Tower.Tm n}

/-- A motive, a value at zero and a step, typed at their types, are a typed
substitution of the recursor's telescope. -/
theorem recArgs_substMor (tp : Typed T.R Δ p (.pi numT U0))
    (tz : Typed T.R Δ z (.app p zeroNative)) (ts : Typed T.R Δ s (vstepType p)) :
    SubstMor T.R numRecTelescope Δ (recArgs p z s) :=
  SubstMor.cons (SubstMor.cons (SubstMor.cons (fun i => Fin.elim0 i) tp) tz) ts

include ext

/-- The recursor applied to a motive, a value at zero and a step. -/
theorem numRec_prefix_typed (tp : Typed T.R Δ p (.pi numT U0))
    (tz : Typed T.R Δ z (.app p zeroNative)) (ts : Typed T.R Δ s (vstepType p)) :
    Typed T.R Δ (.app (.app (.app (.const numRecName) p) z) s)
      (.pi numT (.app (Presentation.rename wk p) (.var 0))) :=
  Typed.telescope_apply (X := .pi numT (.app (.var 3) (.var 0)))
    (recArgs_substMor tp tz ts) (ext.typed rules_numRec_typed)

omit ext Δ z s in
/-- The motive's codomain instantiated at a number. -/
theorem inst0_motiveApp (b : Tower.Tm n) :
    Presentation.inst0 b (.app (Presentation.rename wk p) (.var 0)) = .app p b := by
  show Tm.app (Presentation.inst0 b (Presentation.rename wk p)) b = _
  rw [inst0_rename_wk]

/-- A full application of the recursor. -/
theorem numRec_app_typed (tp : Typed T.R Δ p (.pi numT U0))
    (tz : Typed T.R Δ z (.app p zeroNative)) (ts : Typed T.R Δ s (vstepType p))
    {b : Tower.Tm n} (tb : Typed T.R Δ b numT) : Typed T.R Δ (numRecApp p z s b) (.app p b) := by
  have h := Derivable.appElim (B := .app (Presentation.rename wk p) (.var 0))
    (numRec_prefix_typed ext tp tz ts) tb
  rwa [inst0_motiveApp] at h

omit z s in
/-- The motive at two equal numbers gives equal types. -/
theorem motive_typeEq (tp : Typed T.R Δ p (.pi numT U0)) {b b' : Tower.Tm n}
    (equal : Equal T.R Δ b b' numT) : TypeEq T.R Δ (.app p b) (.app p b') :=
  ⟨_, ext.isUniverse_zero, .appCong (B := U0) (.refl tp) equal⟩

/-- **Reducing the number of a full application of the recursor**, at the
motive's value at the number. -/
theorem numRec_scrutinee_red (tp : Typed T.R Δ p (.pi numT U0))
    (tz : Typed T.R Δ z (.app p zeroNative)) (ts : Typed T.R Δ s (vstepType p))
    {b b' : Tower.Tm n} (red : RedTm T.R T.roles Δ b b' numT) :
    RedTm T.R T.roles Δ (numRecApp p z s b) (numRecApp p z s b') (.app p b) :=
  ⟨WhRed.scrutinee (before := [p, z, s]) (after := []) ext.roles_numRec rfl red.red,
    numRec_app_typed ext tp tz ts red.source,
    Typed.convType (numRec_app_typed ext tp tz ts red.target)
      (motive_typeEq ext tp (.symm red.equal)),
    by
      have h := Derivable.appCong (B := .app (Presentation.rename wk p) (.var 0))
        (.refl (numRec_prefix_typed ext tp tz ts)) red.equal
      rwa [inst0_motiveApp] at h⟩

end Typings

/-- The recursor at zero returns its value at zero, in the executable package. -/
theorem rules_numRec_zero {n : Nat} (p z s : Tower.Tm n) :
    rules.computation.step (numRecApp p z s zeroNative) z :=
  equation_sound (equation_listed 5 (by decide) rfl) (consSub s (consSub z fun _ => p))

/-- The recursor at a successor applies the step to the recursive call, in the
executable package. -/
theorem rules_numRec_suc {n : Nat} (p z s a : Tower.Tm n) :
    rules.computation.step (numRecApp p z s (sucNative a)) (.app (.app s a) (numRecApp p z s a)) :=
  equation_sound (equation_listed 6 (by decide) rfl) (consSub a (consSub s (consSub z fun _ => p)))

section Model

variable (X : TExtension) (v : Nat → Nat) {T : RealizerSide Tower.Head ℕ}

/-! ## Values -/

/-- Numbers with a common shape are related at every denotation of the numbers. -/
theorem num_rel {m : Nat} {ξ : World (nmodel X v T).reading m} {a b : Tower.Tm m}
    {sh : NumShape} (left : X.VShape v a sh) (right : X.VShape v b sh)
    {PA : NPack (nmodel X v T) m} (den : DenN (nmodel X v T) ξ numT PA) :
    PA.rel a b := by
  rw [num_den X v den]
  exact ValueSide.numIndPack_rel.mpr ⟨sh, left, right⟩

/-- A motive related to another at `num → w` sends numbers with a common shape
to types related in the universe `w`. -/
theorem motive_related {w : Tower.Head} (hw : (nmodel X v T).rules.isUniverse w)
    {m : Nat} {ξ : World (nmodel X v T).reading m}
    {RP : NPack (nmodel X v T) m}
    (denP : DenN (nmodel X v T) ξ (.pi numT (.head w)) RP) {P P' : Tower.Tm m}
    (related : RP.rel P P') {a b : Tower.Tm m} {sh : NumShape} (left : X.VShape v a sh)
    (right : X.VShape v b sh) :
    (ValueSide.universeAt (nmodel X v T).value
      ((nmodel X v T).value.levels.level w) ξ).rel (.app P a) (.app P' b) := by
  have laws := (nmodel_laws X v T).value
  obtain ⟨RU, denU, types⟩ := ValueSide.DenS.pi_app_exists laws denP related
    fun den => num_rel X v left right den
  have denU' : DenN (nmodel X v T) ξ (.head w) RU := denU
  rwa [ValueSide.DenS.sort_inv laws hw denU'] at types

/-- At numbers with a common shape, a motive has one denotation. -/
theorem motive_den {w : Tower.Head} (hw : (nmodel X v T).rules.isUniverse w)
    {m : Nat} {ξ : World (nmodel X v T).reading m}
    {RP : NPack (nmodel X v T) m}
    (denP : DenN (nmodel X v T) ξ (.pi numT (.head w)) RP) {P : Tower.Tm m}
    (relP : RP.Val P) {a b : Tower.Tm m} {sh : NumShape} (left : X.VShape v a sh)
    (right : X.VShape v b sh) :
    ∃ R : NPack (nmodel X v T) m, DenN (nmodel X v T) ξ (.app P a) R ∧
      DenN (nmodel X v T) ξ (.app P b) R := by
  obtain ⟨R, first, second, -⟩ :=
    ValueSide.universeAt.den (motive_related X v hw denP relP left right)
  exact ⟨R, ⟨_, first⟩, ⟨_, second⟩⟩

/-- A step related to another at `Π n : num. P n → P (suc n)`, applied to
numbers with a common shape and to values related at the motive, gives values
related at the motive at the successor. -/
theorem step_related {m : Nat} {ξ : World (nmodel X v T).reading m}
    {P s s' : Tower.Tm m} {RS : NPack (nmodel X v T) m}
    (denS : DenN (nmodel X v T) ξ (vstepType P) RS) (relS : RS.rel s s')
    {a b h h' : Tower.Tm m} {sh : NumShape} (left : X.VShape v a sh) (right : X.VShape v b sh)
    (values : ∀ {R : NPack (nmodel X v T) m},
      DenN (nmodel X v T) ξ (.app P a) R → R.rel h h')
    {R : NPack (nmodel X v T) m}
    (denSuc : DenN (nmodel X v T) ξ (.app P (sucNative a)) R) :
    R.rel (.app (.app s a) h) (.app (.app s' b) h') := by
  have laws := (nmodel_laws X v T).value
  obtain ⟨R₁, den₁, related₁⟩ := ValueSide.DenS.pi_app_exists laws denS relS
    fun den => num_rel X v left right den
  rw [vinst0_stepCod] at den₁
  obtain ⟨R₂, den₂, related₂⟩ := ValueSide.DenS.pi_app_exists laws den₁ related₁ values
  rw [vinst0_sucMotive] at den₂
  rw [ValueSide.DenS.deterministic laws denSuc den₂]
  exact related₂

/-- **The recursor's values**: at a motive related to itself at `num → w`,
related values at zero and related steps, applied to numbers with a common
shape, the recursor gives values related at the motive at the first number. -/
theorem numRec_related {w : Tower.Head} (hw : (nmodel X v T).rules.isUniverse w)
    {m : Nat} {ξ : World (nmodel X v T).reading m} {P z z' s s' : Tower.Tm m}
    {RP RZ RS : NPack (nmodel X v T) m}
    (denP : DenN (nmodel X v T) ξ (.pi numT (.head w)) RP) (relP : RP.Val P)
    (denZ : DenN (nmodel X v T) ξ (.app P zeroNative) RZ) (relZ : RZ.rel z z')
    (denS : DenN (nmodel X v T) ξ (vstepType P) RS) (relS : RS.rel s s')
    (P' : Tower.Tm m) :
    ∀ (sh : NumShape) {t t' : Tower.Tm m}, X.VShape v t sh → X.VShape v t' sh →
      ∀ {R : NPack (nmodel X v T) m}, DenN (nmodel X v T) ξ (.app P t) R →
        R.rel (numRecApp P z s t) (numRecApp P' z' s' t') := by
  have laws := (nmodel_laws X v T).value
  intro sh
  induction sh with
  | zero =>
      intro t t' ht ht' R den
      cases ht with
      | zero red =>
          cases ht' with
          | zero red' =>
              obtain ⟨R₀, denT, denZero⟩ := motive_den X v hw denP relP
                (b := zeroNative) (.zero red) (.zero .refl)
              rw [ValueSide.DenS.deterministic laws den denT]
              have expansive := ValueSide.DenS.expansive laws denT
              refine expansive.left (Relation.ReflTransGen.tail (X.numRec_scrutinee v P z s red)
                (X.numRec_zero_step v P z s)) ?_
              refine expansive.right (Relation.ReflTransGen.tail
                (X.numRec_scrutinee v P' z' s' red') (X.numRec_zero_step v P' z' s')) ?_
              rw [ValueSide.DenS.deterministic laws denZero denZ]
              exact relZ
  | suc sh ih =>
      intro t t' ht ht' R den
      cases ht with
      | @suc _ a _ red ha =>
          cases ht' with
          | @suc _ a' _ red' ha' =>
              obtain ⟨R₁, denT, denSuc⟩ := motive_den X v hw denP relP
                (b := sucNative a) (.suc red ha) (.suc .refl ha)
              rw [ValueSide.DenS.deterministic laws den denT]
              have expansive := ValueSide.DenS.expansive laws denT
              refine expansive.left (Relation.ReflTransGen.tail (X.numRec_scrutinee v P z s red)
                (X.numRec_suc_step v P z s a)) ?_
              refine expansive.right (Relation.ReflTransGen.tail
                (X.numRec_scrutinee v P' z' s' red') (X.numRec_suc_step v P' z' s' a')) ?_
              exact step_related X v denS relS ha ha' (ih ha ha') denSuc
  | star =>
      intro t t' ht ht' R den
      cases ht with
      | star red daimonic =>
          cases ht' with
          | star red' daimonic' =>
              have expansive := ValueSide.DenS.expansive laws den
              exact expansive.left (X.numRec_scrutinee v P z s red)
                (expansive.right (X.numRec_scrutinee v P' z' s' red')
                  (ValueSide.DenS.daimonic_related laws den (X.numRec_daimonic v P z s daimonic)
                    (X.numRec_daimonic v P' z' s' daimonic')))

section Realizers

variable (ext : OverRules T)
include ext

/-! ## Realizers -/

/-- **The recursor's realizers.** At a motive, a value at zero and a step with
valid values and related realizers, the recursor applied to the realizers and to
realizers of a number of a shape is related to its application at the second
realizers by the realizers of the recursor's value at the number: by induction
on the shape, the realizers reaching neutral terms, `zero`, or `suc` of the
predecessor's realizers. -/
theorem numRec_real {m r : Nat} {ξ : World (nmodel X v T).reading m}
    {Δ : Tower.Ctx r} (formed : CtxFormed T.R Δ) {P Z S : Tower.Tm m}
    {RP RZ RS : NPack (nmodel X v T) m}
    (denP : DenN (nmodel X v T) ξ (.pi numT U0) RP) (relP : RP.Val P)
    (denZ : DenN (nmodel X v T) ξ (.app P zeroNative) RZ) (relZ : RZ.Val Z)
    (denS : DenN (nmodel X v T) ξ (vstepType P) RS) (relS : RS.Val S)
    {p z s p' z' s' : Tower.Tm r} (realP : (RP.real P).rel Δ (.pi numT U0) p p')
    (realZ : (RZ.real Z).rel Δ (.app p zeroNative) z z')
    (realS : (RS.real S).rel Δ (vstepType p) s s')
    (tz' : Typed T.R Δ z' (.app p' zeroNative)) (ts' : Typed T.R Δ s' (vstepType p'))
    (typeS : IsType T.R Δ (vstepType p)) :
    ∀ (sh : NumShape) {a : Tower.Tm m}, X.VShape v a sh → ∀ {t t' : Tower.Tm r},
      NumShapeRel T numN zeroN sucN sh Δ numT t t' →
      ∀ {Q : NPack (nmodel X v T) m}, DenN (nmodel X v T) ξ (.app P a) Q →
        (Q.real (numRecApp P Z S a)).rel Δ (.app p t) (numRecApp p z s t)
          (numRecApp p' z' s' t') := by
  have laws := nmodel_laws X v T
  have vlaws := laws.value
  have hw : (nmodel X v T).rules.isUniverse (.sort Tower.zero) := LevelTower.IsUniverse.sort _
  have levels := T.levels
  obtain ⟨tp, tp'⟩ := ECand.typed _ realP
  obtain ⟨tz, -⟩ := ECand.typed _ realZ
  obtain ⟨ts, -⟩ := ECand.typed _ realS
  have eP : Equal T.R Δ p p' (.pi numT U0) := ECand.equal _ realP
  -- The motive at equal numbers, on either side, gives equal types.
  have here : ∀ {b b' : Tower.Tm r}, Equal T.R Δ b b' numT →
      TypeEq T.R Δ (.app p b) (.app p b') := fun e => motive_typeEq ext tp e
  have there : ∀ {b b' : Tower.Tm r}, Equal T.R Δ b b' numT →
      TypeEq T.R Δ (.app p' b) (.app p b') := fun e =>
    ⟨_, ext.isUniverse_zero, .appCong (B := U0) (.symm eP) e⟩
  -- Realizers reaching neutral terms: both applications reach neutral spines.
  have neutralCase : ∀ {a : Tower.Tm m} {t t' : Tower.Tm r},
      NeRel T Δ numT t t' →
      ∀ {Q : NPack (nmodel X v T) m},
        (Q.real (numRecApp P Z S a)).rel Δ (.app p t) (numRecApp p z s t)
          (numRecApp p' z' s' t') := by
    intro a t t' ne Q
    have ett' : Equal T.R Δ t t' numT := T.laws.convTm_sound (NeRel.escape ne)
    obtain ⟨w, w', r₀, r₀', nw, nw', cv⟩ := ne
    have redN := numRec_scrutinee_red ext tp tz ts r₀
    have redN' := (numRec_scrutinee_red ext tp' tz' ts' r₀').conv (there (.symm ett'))
    have hN : Neutral T.roles (numRecApp p z s w) :=
      Neutral.stuck_single (before := [p, z, s]) (after := []) ext.roles_numRec rfl nw
    have hN' : Neutral T.roles (numRecApp p' z' s' w') :=
      Neutral.stuck_single (before := [p', z', s']) (after := []) ext.roles_numRec rfl nw'
    have conv : ∀ i, T.E.convTm Δ (consSub w (recArgs p z s) i) (consSub w' (recArgs p' z' s') i)
        (Presentation.subst (consSub w (recArgs p z s))
          (Ctx.lookup (.snoc numRecTelescope numT) i)) := by
      intro i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
        (fun l => Fin.cases ?_ (fun o => o.elim0) l) k) j) i
      · exact T.laws.convTm_of_convNe (.inl nw) (.inl nw') cv
      · exact ECand.escape _ realS
      · exact ECand.escape _ realZ
      · exact ECand.escape _ realP
    have spine := convNe_telescope_apply (S := T.toSetting) T.laws
      (Θ := .snoc numRecTelescope numT)
      (X := .app (.var 3) (.var 0)) conv (T.laws.convNe_const numRecName (ext.typed rules_numRec_typed))
    change T.E.convNe Δ (numRecApp p z s w) (numRecApp p' z' s' w') (.app p w) at spine
    exact ECand.expand _ redN redN' (ECand.neutral _ hN hN' redN.target redN'.target
      (T.laws.convNe_conv spine (here (.symm r₀.equal))))
  intro sh
  induction sh with
  | zero =>
      intro a ha t t' ht Q den
      rcases ht with ne | ⟨-, r₀, r₀', cv⟩
      · exact neutralCase ne
      cases ha with
      | zero red =>
          have ett' : Equal T.R Δ t t' numT := T.laws.convTm_sound cv
          obtain ⟨R₀, denT, denZero⟩ := motive_den X v hw denP relP
            (b := zeroNative) (.zero red) (.zero .refl)
          obtain rfl := ValueSide.DenS.deterministic vlaws den denT
          obtain rfl := ValueSide.DenS.deterministic vlaws denZero denZ
          have value : Q.rel (numRecApp P Z S a) Z :=
            (ValueSide.DenS.expansive vlaws den).left
              (Relation.ReflTransGen.tail (X.numRec_scrutinee v P Z S red)
                (X.numRec_zero_step v P Z S)) relZ
          rw [ValueSide.DenS.real_eq_of_rel vlaws den value]
          -- Both applications compute to the realizers of the value at zero.
          have zeroT : TypeEq T.R Δ (.app p zeroNative) (.app p t) := here (.symm r₀.equal)
          have red := (numRec_scrutinee_red ext tp tz ts r₀).trans
            (RedTm.root (ext.step (rules_numRec_zero p z s))
              (Typed.convType (numRec_app_typed ext tp tz ts r₀.target) zeroT)
              (Typed.convType tz zeroT))
          have zeroT' : TypeEq T.R Δ (.app p' zeroNative) (.app p t) := there (.symm r₀.equal)
          have red' := ((numRec_scrutinee_red ext tp' tz' ts' r₀').conv (there (.symm ett'))).trans
            (RedTm.root (ext.step (rules_numRec_zero p' z' s'))
              (Typed.convType (numRec_app_typed ext tp' tz' ts' r₀'.target) zeroT')
              (Typed.convType tz' zeroT'))
          exact ECand.expand _ red red' (ECand.conv _ formed zeroT realZ)
  | suc sh ih =>
      intro a ha t t' ht Q den
      rcases ht with ne | ⟨-, b, b', r₀, r₀', cv, hb⟩
      · exact neutralCase ne
      cases ha with
      | @suc _ c _ red hc =>
          have ett' : Equal T.R Δ t t' numT := T.laws.convTm_sound cv
          obtain ⟨R₁, denT, denSuc⟩ := motive_den X v hw denP relP
            (b := sucNative c) (.suc red hc) (.suc .refl hc)
          obtain rfl := ValueSide.DenS.deterministic vlaws den denT
          have values : ∀ {R : NPack (nmodel X v T) m},
              DenN (nmodel X v T) ξ (.app P c) R →
                R.rel (numRecApp P Z S c) (numRecApp P Z S c) :=
            fun den' => numRec_related X v hw denP relP denZ relZ denS relS P sh hc hc
              den'
          have value : Q.rel (numRecApp P Z S a) (.app (.app S c) (numRecApp P Z S c)) :=
            (ValueSide.DenS.expansive vlaws den).left
              (Relation.ReflTransGen.tail (X.numRec_scrutinee v P Z S red)
                (X.numRec_suc_step v P Z S c))
              (step_related X v denS relS hc hc values denSuc)
          rw [ValueSide.DenS.real_eq_of_rel vlaws den value]
          -- The step's realizers applied to the predecessor's realizers.
          obtain ⟨-, typeCod⟩ := IsType.pi_parts typeS
          obtain ⟨u, hu, tCod⟩ := typeCod
          have hbReal := (num_real X v ext ⟨0, num_interp X v 0 ξ⟩ hc Δ numT
            b b').mpr hb
          have tb : Typed T.R Δ b numT := (ECand.typed _ hbReal).1
          have typeStep : IsType T.R Δ (.pi (.app p b)
              (.app (Presentation.rename wk p) (sucNative (Presentation.rename wk b)))) := by
            have h := Typed.instantiate tCod tb
            rw [vinst0_stepCod] at h
            exact ⟨u, hu, h⟩
          obtain ⟨PB, denB, -⟩ := ValueSide.DenS.pi_app_exists vlaws denS relS
            fun d => num_rel X v hc hc d
          have first := DenN.pi_app_real laws denS formed (RedTy.refl typeS) realS
            (fun d => ⟨num_rel X v hc hc d,
              (num_real X v ext d hc Δ numT b b').mpr hb⟩) denB
          rw [vinst0_stepCod] at denB first
          have denSuc' : DenN (nmodel X v T) ξ (Presentation.inst0 (numRecApp P Z S c)
              (.app (Presentation.rename wk P) (sucNative (Presentation.rename wk c)))) Q := by
            rw [vinst0_sucMotive]
            exact denSuc
          have second := DenN.pi_app_real laws denB formed (RedTy.refl typeStep) first
            (fun d => ⟨values d, ih hc hb d⟩) denSuc'
          rw [vinst0_sucMotive] at second
          -- Both applications compute to the step's realizers applied to the
          -- predecessor's realizers and to the recursive calls.
          obtain ⟨tStep, tStep'⟩ := ECand.typed _ second
          have sucT : TypeEq T.R Δ (.app p (sucNative b)) (.app p t) := here (.symm r₀.equal)
          have red := (numRec_scrutinee_red ext tp tz ts r₀).trans
            (RedTm.root (ext.step (rules_numRec_suc p z s b))
              (Typed.convType (numRec_app_typed ext tp tz ts r₀.target) sucT)
              (Typed.convType tStep sucT))
          have sucT' : TypeEq T.R Δ (.app p' (sucNative b')) (.app p t) :=
            there (.trans (.symm r₀'.equal) (.symm ett'))
          have red' := ((numRec_scrutinee_red ext tp' tz' ts' r₀').conv (there (.symm ett'))).trans
            (RedTm.root (ext.step (rules_numRec_suc p' z' s' b'))
              (Typed.convType (numRec_app_typed ext tp' tz' ts' r₀'.target) sucT')
              (Typed.convType tStep' sucT))
          exact ECand.expand _ red red' (ECand.conv _ formed sucT second)
  | star =>
      intro a ha t t' ht Q den
      exact neutralCase ht

/-! ## Validity -/

/-- The stage of the numbers and their constructors is sound for the model. -/
theorem ctorStage_typedSoundN : TypedSoundN ctorStage (nmodel X v T) :=
  stage_typedSoundN_of X v ext fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
    · exact valid_num X v ext
    · exact valid_zero X v ext
    · exact valid_suc X v ext

/-- **The recursor on the numbers is valid** in the conversion model. -/
theorem valid_numRec :
    ValidTmN (nmodel X v T) .nil (.const numRecName) numRecType := by
  have laws := nmodel_laws X v T
  have vlaws := laws.value
  have hw : (nmodel X v T).rules.isUniverse (.sort Tower.zero) := LevelTower.IsUniverse.sort _
  obtain ⟨validT, partsT, _⟩ :=
    Derivable.validTN (ctorStage_typedSoundN X v ext) numRecType_typed trivial
  have validType : ValidTyN (nmodel X v T) .nil numRecType :=
    validT.validTy (LevelTower.IsUniverse.sort _) (ext.isUniverse_sort _)
  obtain ⟨ctx, validResult, _⟩ := ValidTyN.close_parts (.snoc numRecTelescope numT)
    (C := .app (.var 3) (.var 0)) validType partsT
  have typed : Typed T.R .nil (.const numRecName) numRecType := by
    have h := ext.typed (rules_numRec_typed (Γ := .nil))
    rwa [TelescopeAbstraction.liftClosed_zero] at h
  refine ValidTmN.close laws (.snoc numRecTelescope numT) (C := .app (.var 3) (.var 0))
    (f := .const numRecName) validType partsT typed
    (fun args short => .inr (.inr ⟨numRecName, args, 4, .inr ⟨_, ext.roles_numRec⟩, short, rfl⟩))
    ⟨validResult, fun {m r ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  have typed' := EqSubstN.substMor_right laws ctx.valid e
  obtain ⟨-, -, -, typesS⟩ := (ctx.lookup 1).1 e
  have typeS : IsType T.R Δ (vstepType (ς 3)) := typesS.left
  obtain ⟨⟨⟨⟨formed, RP, denP, relP, realP⟩, RZ, denZ, relZ, realZ⟩, RS, denS, relS, realS⟩,
    RT, denT, relT, realT⟩ := e
  change DenN (nmodel X v T) ξ (.pi numT U0) RP at denP
  change RP.rel (σ 3) (σ' 3) at relP
  change (RP.real (σ 3)).rel Δ (.pi numT U0) (ς 3) (ς' 3) at realP
  change DenN (nmodel X v T) ξ (.app (σ 3) zeroNative) RZ at denZ
  change RZ.rel (σ 2) (σ' 2) at relZ
  change (RZ.real (σ 2)).rel Δ (.app (ς 3) zeroNative) (ς 2) (ς' 2) at realZ
  change DenN (nmodel X v T) ξ (vstepType (σ 3)) RS at denS
  change RS.rel (σ 1) (σ' 1) at relS
  change (RS.real (σ 1)).rel Δ (vstepType (ς 3)) (ς 1) (ς' 1) at realS
  change DenN (nmodel X v T) ξ numT RT at denT
  change RT.rel (σ 0) (σ' 0) at relT
  change (RT.real (σ 0)).rel Δ numT (ς 0) (ς' 0) at realT
  change DenN (nmodel X v T) ξ (.app (σ 3) (σ 0)) P at den
  show P.rel (numRecApp (σ 3) (σ 2) (σ 1) (σ 0)) (numRecApp (σ' 3) (σ' 2) (σ' 1) (σ' 0)) ∧
    (P.real (numRecApp (σ 3) (σ 2) (σ 1) (σ 0))).rel Δ (.app (ς 3) (ς 0))
      (numRecApp (ς 3) (ς 2) (ς 1) (ς 0)) (numRecApp (ς' 3) (ς' 2) (ς' 1) (ς' 0))
  rw [num_den X v denT] at relT
  obtain ⟨sh, shape, shape'⟩ := ValueSide.numIndPack_rel.mp relT
  have relP' := ValueSide.DenS.refl_left vlaws denP relP
  have tz' : Typed T.R Δ (ς' 2) (.app (ς' 3) zeroNative) := typed' 2
  have ts' : Typed T.R Δ (ς' 1) (vstepType (ς' 3)) := typed' 1
  exact ⟨numRec_related X v hw denP relP' denZ relZ denS relS (σ' 3) sh shape shape' den,
    numRec_real X v ext formed denP relP' denZ (ValueSide.DenS.refl_left vlaws denZ relZ)
      denS (ValueSide.DenS.refl_left vlaws denS relS) realP realZ realS tz' ts' typeS sh shape
      ((num_real X v ext denT shape Δ numT _ _).mp realT) den⟩

end Realizers

end Model

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
