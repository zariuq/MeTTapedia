import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSteps
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelTypings

/-!
# The recursor on the numbers in the transport value model

The recursor `num-rec P z s n` computes at `zero` to `z`, and at `suc m` to
`s m (num-rec P z s m)`, on the value side of `vmodel` and on the realizer side
alike. It is a valid term of
`Π P : num → w. P zero → (Π n : num. P n → P (suc n)) → Π n : num. P n` for
every universe `w` (`valid_numRecS_at`), the declared type `numRecType` being
the instance at the lowest universe (`vmodel_valid_numRec`):

* A motive related to itself at `num → w` sends numbers with a common shape to
  types related in the universe `w`, so it has one denotation at such numbers.
  No skeleton relation is involved: the universe relation relates types with
  one pack and one shape at any level, so large elimination is the same
  argument as small elimination.
* Values: by induction on the common shape of two related numbers. At zero both
  sides compute to the values at zero, and at a successor to the steps applied
  to the predecessors and to the recursive calls, which are related by
  induction. At the daimon both sides are stuck on it, and every denotation
  relates daimonic terms.
* Realizers: the realizers of the recursor's values at the numbers of a shape
  form a family of candidates indexed by shapes alone, since numbers of one
  shape are related, so they have one denotation of the motive and their values
  have the same realizers. The recursor applied to realizers lies in this
  family at the shape of its number, by induction on the shape: the value at
  zero realizes the base case, and the step's realizer sends a realizer of a
  number of a shape and a member of the family there into the family at the
  successor shape.

A term of a universe is valid by its pack at the universe's level, and the
relation of a denotation is a partial equivalence, so validity asks for nothing
beyond related values and realizers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency (World)
open Presentation.TypedEquality.Impredicative.Realizability (Daimonic)
open SetProfile (zeroNative sucNative)
open Package (numRecName numT numRecType numRecApp)

namespace CodeModel

variable (v : Nat → Nat)

/-! ## The motive and the step -/

/-- The type of the recursor's step at a motive `P`: `Π n : num. P n → P (suc n)`. -/
abbrev vstepType {n : Nat} (P : Tower.Tm n) : Tower.Tm n :=
  .pi numT (.pi (.app (Presentation.rename wk P) (.var 0))
    (.app (Presentation.rename wk (Presentation.rename wk P)) (sucNative (.var 1))))

/-- The step's type at a number `a`: `P a → P (suc a)`. -/
theorem vinst0_stepCod {n : Nat} (P a : Tower.Tm n) :
    Presentation.inst0 a (.pi (.app (Presentation.rename wk P) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk P)) (sucNative (.var 1)))) =
      .pi (.app P a) (.app (Presentation.rename wk P) (sucNative (Presentation.rename wk a))) := by
  show Tm.pi (.app (Presentation.inst0 a (Presentation.rename wk P)) a)
      (.app (Presentation.subst (liftSub (subst0 a))
          (Presentation.rename wk (Presentation.rename wk P)))
        (sucNative (Presentation.rename wk a))) = _
  rw [inst0_rename_wk, subst_liftSub_wk]
  show Tm.pi (.app P a) (.app (Presentation.rename wk
      (Presentation.inst0 a (Presentation.rename wk P))) (sucNative (Presentation.rename wk a))) = _
  rw [inst0_rename_wk]

/-- The motive at the successor of a number, over one more variable,
instantiated at a value. -/
theorem vinst0_sucMotive {n : Nat} (P a h : Tower.Tm n) :
    Presentation.inst0 h (.app (Presentation.rename wk P) (sucNative (Presentation.rename wk a))) =
      .app P (sucNative a) := by
  show Tm.app (Presentation.inst0 h (Presentation.rename wk P))
      (sucNative (Presentation.inst0 h (Presentation.rename wk a))) = _
  rw [inst0_rename_wk, inst0_rename_wk]

/-- A motive related to another at `num → w` sends numbers with a common shape
to types related in the universe `w`. -/
theorem vmotive_related {w : Tower.Head} (hw : (vmodel v).rules.isUniverse w) {m : Nat}
    {ξ : World (vmodel v).reading m} {RP : ValueSide.Pack (vmodel v).value m}
    (denP : ValueSide.DenS (vmodel v).value ξ (.pi numT (.head w)) RP) {P P' : Tower.Tm m}
    (related : RP.rel P P') {a b : Tower.Tm m} {sh : NumShape}
    (left : VShape v a sh) (right : VShape v b sh) :
    (ModelS.universeAt (vmodel v) ((vmodel v).levels.level w) ξ).rel (.app P a)
      (.app P' b) := by
  obtain ⟨RU, denU, types⟩ := ModelS.DenS.pi_app_exists (vmodel_laws v) denP related
    fun den => vnum_rel v left right den
  have denU' : ValueSide.DenS (vmodel v).value ξ (.head w) RU := denU
  rwa [ModelS.DenS.sort_inv (vmodel_laws v) hw denU'] at types

/-- At numbers with a common shape, the motive has one denotation. -/
theorem vmotive_den {w : Tower.Head} (hw : (vmodel v).rules.isUniverse w) {m : Nat}
    {ξ : World (vmodel v).reading m} {RP : ValueSide.Pack (vmodel v).value m}
    (denP : ValueSide.DenS (vmodel v).value ξ (.pi numT (.head w)) RP) {P : Tower.Tm m}
    (relP : RP.rel P P) {a b : Tower.Tm m} {sh : NumShape} (left : VShape v a sh)
    (right : VShape v b sh) :
    ∃ R, ValueSide.DenS (vmodel v).value ξ (.app P a) R ∧
      ValueSide.DenS (vmodel v).value ξ (.app P b) R := by
  obtain ⟨R, first, second, -⟩ :=
    ModelS.universeAt.den (vmotive_related v hw denP relP left right)
  exact ⟨R, ⟨_, first⟩, ⟨_, second⟩⟩

/-- A step related to another at `Π n : num. P n → P (suc n)`, applied to
numbers with a common shape and to values related at the motive, gives values
related at the motive at the successor. -/
theorem vstep_related {m : Nat} {ξ : World (vmodel v).reading m}
    {P s s' : Tower.Tm m} {RS : ValueSide.Pack (vmodel v).value m}
    (denS : ValueSide.DenS (vmodel v).value ξ (vstepType P) RS) (relS : RS.rel s s')
    {a b h h' : Tower.Tm m} {sh : NumShape} (left : VShape v a sh) (right : VShape v b sh)
    (values : ∀ {R : ValueSide.Pack (vmodel v).value m},
      ValueSide.DenS (vmodel v).value ξ (.app P a) R → R.rel h h')
    {R : ValueSide.Pack (vmodel v).value m}
    (denSuc : ValueSide.DenS (vmodel v).value ξ (.app P (sucNative a)) R) :
    R.rel (.app (.app s a) h) (.app (.app s' b) h') := by
  obtain ⟨R₁, den₁, related₁⟩ := ModelS.DenS.pi_app_exists (vmodel_laws v) denS relS
    fun den => vnum_rel v left right den
  rw [vinst0_stepCod] at den₁
  obtain ⟨R₂, den₂, related₂⟩ := ModelS.DenS.pi_app_exists (vmodel_laws v) den₁ related₁ values
  rw [vinst0_sucMotive] at den₂
  rw [ValueSide.DenS.deterministic (vmodel_valueLaws v) denSuc den₂]
  exact related₂

/-! ## Values -/

/-- The recursor at a daimonic number is stuck on the daimon. -/
theorem vnumRec_daimonic {n : Nat} (P z s : Tower.Tm n) {u : Tower.Tm n}
    (daimonic : Daimonic (vmodel v).roles (vmodel v).star u) :
    Daimonic (vmodel v).roles (vmodel v).star (numRecApp P z s u) :=
  Daimonic.stuck (before := [P, z, s]) (after := []) tmodelRoles_numRec rfl daimonic

/-- The recursor at a motive related to itself at `num → w`, related values at
zero and related steps, applied to numbers with a common shape, gives values
related at the motive at the first number. -/
theorem vnumRec_related {w : Tower.Head} (hw : (vmodel v).rules.isUniverse w) {m : Nat}
    {ξ : World (vmodel v).reading m}
    {P z z' s s' : Tower.Tm m} {RP RZ RS : ValueSide.Pack (vmodel v).value m}
    (denP : ValueSide.DenS (vmodel v).value ξ (.pi numT (.head w)) RP) (relP : RP.rel P P)
    (denZ : ValueSide.DenS (vmodel v).value ξ (.app P zeroNative) RZ) (relZ : RZ.rel z z')
    (denS : ValueSide.DenS (vmodel v).value ξ (vstepType P) RS) (relS : RS.rel s s')
    (P' : Tower.Tm m) :
    ∀ (sh : NumShape) {t t' : Tower.Tm m}, VShape v t sh → VShape v t' sh →
      ∀ {R : ValueSide.Pack (vmodel v).value m},
        ValueSide.DenS (vmodel v).value ξ (.app P t) R →
          R.rel (numRecApp P z s t) (numRecApp P' z' s' t') := by
  have laws := vmodel_valueLaws v
  intro sh
  induction sh with
  | zero =>
      intro t t' ht ht' R den
      cases ht with
      | zero red =>
          cases ht' with
          | zero red' =>
              obtain ⟨R₀, denT, denZero⟩ :=
                vmotive_den v hw denP relP (b := zeroNative) (.zero red) (.zero .refl)
              rw [ValueSide.DenS.deterministic laws den denT]
              have expansive := ValueSide.DenS.expansive laws denT
              refine expansive.left (Relation.ReflTransGen.tail (vnumRec_scrutinee v P z s red)
                (vnumRec_zero_step v P z s)) ?_
              refine expansive.right (Relation.ReflTransGen.tail
                (vnumRec_scrutinee v P' z' s' red') (vnumRec_zero_step v P' z' s')) ?_
              rw [ValueSide.DenS.deterministic laws denZero denZ]
              exact relZ
  | suc sh ih =>
      intro t t' ht ht' R den
      cases ht with
      | @suc _ a _ red ha =>
          cases ht' with
          | @suc _ a' _ red' ha' =>
              obtain ⟨R₁, denT, denSuc⟩ :=
                vmotive_den v hw denP relP (b := sucNative a) (.suc red ha) (.suc .refl ha)
              rw [ValueSide.DenS.deterministic laws den denT]
              have expansive := ValueSide.DenS.expansive laws denT
              refine expansive.left (Relation.ReflTransGen.tail (vnumRec_scrutinee v P z s red)
                (vnumRec_suc_step v P z s a)) ?_
              refine expansive.right (Relation.ReflTransGen.tail
                (vnumRec_scrutinee v P' z' s' red') (vnumRec_suc_step v P' z' s' a')) ?_
              exact vstep_related v denS relS ha ha' (ih ha ha') denSuc
  | star =>
      intro t t' ht ht' R den
      cases ht with
      | star red daimonic =>
          cases ht' with
          | star red' daimonic' =>
              have expansive := ValueSide.DenS.expansive laws den
              exact expansive.left (vnumRec_scrutinee v P z s red)
                (expansive.right (vnumRec_scrutinee v P' z' s' red')
                  (ValueSide.DenS.daimonic_related laws den (vnumRec_daimonic v P z s daimonic)
                    (vnumRec_daimonic v P' z' s' daimonic')))

/-! ## Realizers -/

/-- On the realizer side the recursor computes, as on the value side, at four
arguments with the number as its scrutinee. -/
theorem objectRoles_numRecV :
    objectRoles numRecName = .computes 4 (.split 3 .constructor fun _ => .leaf) :=
  objectRoles_of_roles roles_numRec nofun

/-- The numbers of a shape, each with a denotation of the motive there. -/
abbrev VMotiveAt {m : Nat} (ξ : World (vmodel v).reading m) (P : Tower.Tm m)
    (sh : NumShape) : Type :=
  (t : Tower.Tm m) ×' (Q : ValueSide.Pack (vmodel v).value m) ×'
    (VShape v t sh ∧ ValueSide.DenS (vmodel v).value ξ (.app P t) Q)

/-- The realizers of the recursor's values at the numbers of a shape: at every
number of the shape and every denotation of the motive there, the realizers of
the recursor's value. -/
def vnumRecReal {m : Nat} (ξ : World (vmodel v).reading m) (P z s : Tower.Tm m)
    (sh : NumShape) : objectRealizers.Cand :=
  KCand.inter objectReflects fun x : VMotiveAt v ξ P sh =>
    (x.2.1.real (numRecApp P z s x.1) : objectRealizers.Cand)

/-- The recursor applied to realizers of a motive, a value at zero, a step and a
number of some shape realizes the recursor's values at the numbers of that
shape. -/
theorem vnumRec_real {w : Tower.Head} (hw : (vmodel v).rules.isUniverse w) {m r : Nat}
    {ξ : World (vmodel v).reading m}
    {P z s : Tower.Tm m} {RP RZ RS : ValueSide.Pack (vmodel v).value m}
    (denP : ValueSide.DenS (vmodel v).value ξ (.pi numT (.head w)) RP) (relP : RP.rel P P)
    (denZ : ValueSide.DenS (vmodel v).value ξ (.app P zeroNative) RZ) (relZ : RZ.rel z z)
    (denS : ValueSide.DenS (vmodel v).value ξ (vstepType P) RS) (relS : RS.rel s s)
    {p z₀ s₀ : Tower.Tm r} (sp : SN objectRules p) (realZ : (RZ.real z).mem z₀)
    (realS : (RS.real s).mem s₀) (sh : NumShape) {a : Tower.Tm r} (ha : (VNumReal sh).mem a) :
    (vnumRecReal v ξ P z s sh).mem (appSpine (.const numRecName) [p, z₀, s₀, a]) := by
  have laws := vmodel_valueLaws v
  have related := vnumRec_related v hw denP relP denZ relZ denS relS P
  refine KCand.recursor_mem objectShape objectReflects objectNumerals (vnumRecReal v ξ P z s)
    objectRoles_numRecV objectStep_numRec sh sp ?_ (KCand.sn _ realS) ?_ ha
  · -- The base case: at zero the recursor's value is related to the value at zero.
    refine ⟨KCand.sn _ realZ, fun ⟨t, Q, shape, den⟩ => ?_⟩
    change (Q.real (numRecApp P z s t)).mem z₀
    cases shape with
    | zero red =>
        obtain ⟨R, denT, denZero⟩ :=
          vmotive_den v hw denP relP (b := zeroNative) (.zero red) (.zero .refl)
        rw [ValueSide.DenS.deterministic laws den denT,
          ValueSide.DenS.deterministic laws denZero denZ]
        have value : RZ.rel (numRecApp P z s t) z :=
          (ValueSide.DenS.expansive laws denZ).left
            (Relation.ReflTransGen.tail (vnumRec_scrutinee v P z s red)
              (vnumRec_zero_step v P z s)) relZ
        rw [ValueSide.DenS.real_eq_of_rel laws denZ value]
        exact realZ
  · -- The step is realized: at a successor the recursor's value is related to the
    -- step's value, which the step's realizer realizes.
    intro sh' k ρ b r' hb hr'
    have mem : ∀ x : VMotiveAt v ξ P (.suc sh'),
        (x.2.1.real (numRecApp P z s x.1)).mem
          (.app (.app (Presentation.rename ρ s₀) b) r') := by
      rintro ⟨t, Q, shape, den⟩
      change (Q.real (numRecApp P z s t)).mem _
      cases shape with
      | @suc _ c _ red hc =>
          obtain ⟨R, denT, denSuc⟩ :=
            vmotive_den v hw denP relP (b := sucNative c) (.suc red hc) (.suc .refl hc)
          rw [ValueSide.DenS.deterministic laws den denT]
          have values : ∀ {Q' : ValueSide.Pack (vmodel v).value m},
              ValueSide.DenS (vmodel v).value ξ (.app P c) Q' →
                Q'.rel (numRecApp P z s c) (numRecApp P z s c) :=
            fun den' => related sh' hc hc den'
          have value : R.rel (numRecApp P z s t) (.app (.app s c) (numRecApp P z s c)) :=
            (ValueSide.DenS.expansive laws denT).left
              (Relation.ReflTransGen.tail (vnumRec_scrutinee v P z s red)
                (vnumRec_suc_step v P z s c))
              (vstep_related v denS relS hc hc values denSuc)
          rw [ValueSide.DenS.real_eq_of_rel laws denT value]
          obtain ⟨R₁, den₁, -⟩ := ModelS.DenS.pi_app_exists (vmodel_laws v) denS relS
            fun d => vnum_rel v hc hc d
          have first := ModelS.DenS.pi_app_real (vmodel_laws v) denS
            ((RS.real s).rename ρ realS) (fun d => vnum_val v hc d)
            (fun d => (vnum_real v hc d).mpr hb) den₁
          rw [vinst0_stepCod] at den₁
          have denSuc' : ValueSide.DenS (vmodel v).value ξ (Presentation.inst0
              (numRecApp P z s c)
              (.app (Presentation.rename wk P) (sucNative (Presentation.rename wk c)))) R := by
            rw [vinst0_sucMotive]
            exact denSuc
          exact ModelS.DenS.pi_app_real (vmodel_laws v) den₁ first (fun den' => values den')
            (fun den' => hr'.2 ⟨c, _, hc, den'⟩) denSuc'
    obtain ⟨R, denW, -⟩ := vmotive_den v hw denP relP
      (ValueSide.hasShape_shapeTerm (V := (vmodel v).value) (.suc sh'))
      (ValueSide.hasShape_shapeTerm (V := (vmodel v).value) (.suc sh'))
    exact ⟨KCand.sn _ (mem ⟨_, R, ValueSide.hasShape_shapeTerm _, denW⟩), mem⟩

/-! ## Validity -/

/-- **The recursor on the numbers is valid with its motive into every
universe** in the transport value model: large elimination of the numbers. The
validity of the type and of its parts are hypotheses, which the fundamental
lemma of a smaller stage provides. -/
theorem valid_numRecS_at (w : Tower.Head) (hw : (vmodel v).rules.isUniverse w)
    (validType : ModelS.ValidTyS (vmodel v) .nil (numRecTypeAt w))
    (partsType : ModelS.StructuredS (vmodel v) .nil (numRecTypeAt w)) :
    ModelS.ValidTmS (vmodel v) .nil (.const numRecName) (numRecTypeAt w) := by
  have laws := vmodel_valueLaws v
  obtain ⟨_, validResult, _⟩ := ModelS.ValidTyS.close_parts (.snoc (numRecTelescopeAt w) numT)
    (C := .app (.var 3) (.var 0)) validType partsType
  refine ModelS.ValidTmS.close (vmodel_laws v) (.snoc (numRecTelescopeAt w) numT)
    (C := .app (.var 3) (.var 0)) (f := .const numRecName) validType partsType
    ⟨validResult, fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩
  obtain ⟨⟨⟨⟨-, RP, denP, relP, realP⟩, RZ, denZ, relZ, realZ⟩, RS, denS, relS, realS⟩,
    RT, denT, relT, realT⟩ := e
  change ValueSide.DenS (vmodel v).value ξ (.pi numT (.head w)) RP at denP
  change RP.rel (σ 3) (σ' 3) at relP
  change (RP.real (σ 3)).mem (ς 3) at realP
  change ValueSide.DenS (vmodel v).value ξ (.app (σ 3) zeroNative) RZ at denZ
  change RZ.rel (σ 2) (σ' 2) at relZ
  change (RZ.real (σ 2)).mem (ς 2) at realZ
  change ValueSide.DenS (vmodel v).value ξ (vstepType (σ 3)) RS at denS
  change RS.rel (σ 1) (σ' 1) at relS
  change (RS.real (σ 1)).mem (ς 1) at realS
  change ValueSide.DenS (vmodel v).value ξ numT RT at denT
  change RT.rel (σ 0) (σ' 0) at relT
  change (RT.real (σ 0)).mem (ς 0) at realT
  change ValueSide.DenS (vmodel v).value ξ (.app (σ 3) (σ 0)) P at den
  show P.rel (numRecApp (σ 3) (σ 2) (σ 1) (σ 0)) (numRecApp (σ' 3) (σ' 2) (σ' 1) (σ' 0)) ∧
    (P.real (numRecApp (σ 3) (σ 2) (σ 1) (σ 0))).mem
      (appSpine (.const numRecName) [ς 3, ς 2, ς 1, ς 0])
  obtain ⟨sh, shape, shape'⟩ := vnum_shape v denT relT
  have realT' := (vnum_real v shape denT).mp realT
  have relP' := ValueSide.DenS.refl_left laws denP relP
  exact ⟨vnumRec_related v hw denP relP' denZ relZ denS relS (σ' 3) sh shape shape' den,
    (vnumRec_real v hw denP relP' denZ (ValueSide.DenS.refl_left laws denZ relZ) denS
      (ValueSide.DenS.refl_left laws denS relS) (KCand.sn _ realP) realZ realS sh realT').2
      ⟨σ 0, P, shape, den⟩⟩

/-- **The recursor on the numbers is valid** in the transport value model: the
instance of `valid_numRecS_at` at the lowest universe. The validity of its
declared type and of that type's parts are hypotheses, which the fundamental
lemma of a smaller stage provides. -/
theorem vmodel_valid_numRec (validType : ModelS.ValidTyS (vmodel v) .nil numRecType)
    (partsType : ModelS.StructuredS (vmodel v) .nil numRecType) :
    ModelS.ValidTmS (vmodel v) .nil (.const numRecName) numRecType :=
  valid_numRecS_at v (.sort Tower.zero) (Tower.IsUniverse.sort _) validType partsType

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
