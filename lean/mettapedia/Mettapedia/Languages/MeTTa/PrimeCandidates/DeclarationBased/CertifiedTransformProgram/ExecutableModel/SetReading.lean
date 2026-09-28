import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencySound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Model
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Carriers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingCompile
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.TheoremDefinitions

/-!
# The set profile read in the object package

The object package `objectRules` is the executable package with the program's
codes. It reads the set profile's HOL signature (`setReading`):

* the sorts `num` and `set` are the declared types;
* the constants it declares, `zero`, `suc`, `add`, `Power` and `pow`, are read
  as themselves. The other constants of the signature (`Falsum`, `In`,
  `Empty`, `Union`, `Sep`, `Repl`, `Eps_set`, `UnivOf`) are not declared by
  the package and are not read;
* `all@A` and `eq@A` are the profile's instance names, at every simple type.

The package is the reading's package (`setReading_rules`), and it satisfies the
laws of a reading (`setReading_laws`). The profile's defining equations of
addition and the iterated power set are root steps of the executable package
(`setReading_realizes`).

The facts the proof library publishes are realized in the selected typed
judgment of the package:

* reflexivity at every carrier by `λx. refl x` (`reflRealization_typedO`);
* substitution at every carrier by identity elimination at a code motive
  (`substRealizationAt_typedO`);
* induction on the numbers by the recursor at a code motive
  (`inductionRealization_typedO`).

**`Falsum` published by name.** The signature defines `Falsum := ∀p. p`. The
package with the definition publishes `Falsum` by name (`definedRules`, by
`Rules.withTheorem`): a constant of `prop` whose δ-rule steps to `botCode`, the
code of `∀p. p`. The reading with the definition (`definedReading`) reads
`Falsum` as that constant, as the checker spells it, and realizes the
definition by the δ-step (`definedReading_realizes`). Its package is the
extended package (`definedReading_rules`), and its laws are those of the set
reading carried along the extension (`objectRules_defined`), with `Falsum` a
term of `prop` (`falsum_typed`, `definedReading_laws`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative
open Mettapedia.Logic
open Package (jName numRecName U0 numT jType numRecType jApp numRecApp)
open SetProfile (SetBase SetConst numTy)
open IdentityEquality.Realizations (reflRealization substMotive inductionMotive
  inductionRealization)

namespace CodeModel

/-! ## The reading -/

/-- The constants of the set profile the executable package declares. -/
def setConstant : {τ : HOL.Ty SetBase} → SetConst τ → Option (Tower.Tm 0)
  | _, .zero => some (.const zeroN)
  | _, .suc => some (.const sucN)
  | _, .add => some (.const addN)
  | _, .power => some (.const powerN)
  | _, .pow => some (.const powN)
  | _, .falsum | _, .member | _, .empty | _, .union | _, .separation | _, .replacement
  | _, .epsilon | _, .universeOf => none

/-- The set profile read in the object package. -/
def setReading : HOLReading Tower.Head SetBase SetConst where
  codes := programCodes
  base := rules
  sort := fun b => .const (SetProfile.baseName b)
  constant := setConstant
  allName := SetProfile.allName
  eqName := SetProfile.eqName

/-- The reading's package is the object package. -/
theorem setReading_rules : setReading.rules = objectRules := rfl

theorem setReading_carrierAt {n : Nat} (τ : HOL.Ty SetBase) :
    setReading.carrierAt n τ = FormationSensitiveHOLInterface.typeAt SetProfile.types n τ := by
  induction τ generalizing n with
  | prop => rfl
  | base b => rfl
  | arr a b ia ib =>
      simp only [HOLReading.carrierAt, FormationSensitiveHOLInterface.typeAt, ia, ib]

theorem setReading_carrier (τ : HOL.Ty SetBase) : setReading.carrier τ = typeTerm τ :=
  setReading_carrierAt τ

/-! ## The declared constants in the typed judgment -/

section Constants

variable {n : Nat} {Γ : Tower.Ctx n}

theorem set_typedO : Typed objectRules Γ setT Package.U0 :=
  .const (rfl : objectRules.constantType setN = some Package.U0) (.headType (.sort _)) (.sort _)

theorem add_typedO : Typed objectRules Γ (.const addN) (.pi numT (.pi numT numT)) :=
  .const (rfl : objectRules.constantType addN = some addType)
    (piO num_typedO (piO num_typedO num_typedO)) (.sort Tower.zero)

theorem power_typedO : Typed objectRules Γ (.const powerN) (.pi setT setT) :=
  .const (rfl : objectRules.constantType powerN = some powerType)
    (piO set_typedO set_typedO) (.sort Tower.zero)

theorem pow_typedO : Typed objectRules Γ (.const powN) (.pi numT (.pi setT setT)) :=
  .const (rfl : objectRules.constantType powN = some powType)
    (piO num_typedO (piO set_typedO set_typedO)) (.sort Tower.zero)

end Constants

/-! ## The laws -/

/-- **The set profile is a reading of the object package.** Every law is a
fact about `objectRules`; none is assumed. -/
theorem setReading_laws : setReading.Laws where
  quantifier τ := by
    change (SetProfile.allInstance? (SetProfile.allName τ)).map typeTerm =
      some (setReading.carrier τ)
    rw [SetProfile.allInstance?_allName, setReading_carrier]
    rfl
  equation τ := by
    change (if true = true then (SetProfile.eqInstance? (SetProfile.eqName τ)).map typeTerm
      else none) = some (setReading.carrier τ)
    rw [if_pos rfl, SetProfile.eqInstance?_eqName, setReading_carrier]
    rfl
  allName_apart τ := allName_ne_codes τ
  eqName_apart τ := by
    obtain ⟨hp, hh, hi⟩ := eqName_ne_codes τ
    refine ⟨hp, hh, hi, ?_⟩
    change (SetProfile.allInstance? (SetProfile.eqName τ)).map typeTerm = none
    rw [SetProfile.allInstance?_eqName]
    rfl
  imp_apart := ⟨by decide, by decide⟩
  holds_apart := by decide
  proofs_universe := .sort _
  proofs_typed := ⟨_, .sort _, .sort _⟩
  proofs_pi := ⟨_, .sorts Tower.zero Tower.zero, fun _ => Nat.le_of_eq (Nat.max_self _)⟩
  holds_formed := ⟨_, .sort _, piO (raiseO prop_typedO) U0_typedO⟩
  sort_typed b := by
    cases b
    · exact set_typedO
    · exact num_typedO
  const_typed c t found := by
    cases c <;> simp only [setReading, setConstant, reduceCtorEq, Option.some.injEq] at found <;>
      subst found <;>
      first
        | exact zero_typedO
        | exact suc_typedO
        | exact add_typedO
        | exact power_typedO
        | exact pow_typedO

/-! ## The defining equations are root steps -/

/-- The equations of `add` and `pow` of the set profile are root steps of the
executable package, at every instance. -/
theorem setReading_realizes : setReading.Realizes SetProfile.sourceEquations := by
  intro equation mem
  simp only [SetProfile.sourceEquations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl
  · refine ⟨_, _, rfl, rfl, fun (σ : Sub Tower.Head 1 _) => ?_⟩
    exact rules_step (listed 1 (by decide))
      ⟨zeroN, [], consSub (.const zeroN) (consSub (σ 0) fun i => Fin.elim0 i), [], mem_zero,
        rfl, rfl, rfl⟩
  · refine ⟨_, _, rfl, rfl, fun (σ : Sub Tower.Head 2 _) => ?_⟩
    exact rules_step (listed 1 (by decide))
      ⟨sucN, [.recursive],
        consSub (.app (.const sucN) (σ 0)) (consSub (σ 1) fun i => Fin.elim0 i),
        [σ 0], mem_suc, rfl, rfl, rfl⟩
  · refine ⟨_, _, rfl, rfl, fun (σ : Sub Tower.Head 1 _) => ?_⟩
    exact rules_step (listed 2 (by decide))
      ⟨zeroN, [], consSub (σ 0) (consSub (.const zeroN) fun i => Fin.elim0 i), [], mem_zero,
        rfl, rfl, rfl⟩
  · refine ⟨_, _, rfl, rfl, fun (σ : Sub Tower.Head 2 _) => ?_⟩
    exact rules_step (listed 2 (by decide))
      ⟨sucN, [.recursive],
        consSub (σ 0) (consSub (.app (.const sucN) (σ 1)) fun i => Fin.elim0 i),
        [σ 1], mem_suc, rfl, rfl, rfl⟩

/-! ## Identity elimination and the recursor in the typed judgment -/

/-- The telescope `A x P d y e` of `id:eliminate`. -/
abbrev jTelescope : Tower.Ctx 6 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil Package.U0) (.var 0))
    (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) Package.U0)))
    (.app (.app (.var 0) (.var 1)) (.refl (.var 1))))
    (.var 3))
    (.id (.var 4) (.var 3) (.var 0))

theorem jConst_typedO {n : Nat} {Γ : Tower.Ctx n} :
    Typed objectRules Γ (.const jName) (liftClosed jType) := by
  obtain ⟨w, hw, formed⟩ := jType_typed
  exact .const (rfl : objectRules.constantType jName = some jType)
    (Derivable.mono (RulesSub.constantFree objectRules) formed) hw

theorem jSpine_typedO :
    Typed objectRules jTelescope (jApp (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
      (.app (.app (.var 3) (.var 1)) (.var 0)) := by
  have j0 : Typed objectRules jTelescope (.const jName) (liftClosed jType) := jConst_typedO
  rw [Package.jType_eq] at j0
  exact .appElim (.appElim (.appElim (.appElim (.appElim (.appElim j0 (.var 5)) (.var 4))
    (.var 3)) (.var 2)) (.var 1)) (.var 0)

/-- **Identity elimination** at a carrier of the lowest universe:
`id:eliminate A x P d y e : P y e`. -/
theorem j_typedO {n : Nat} {Γ : Tower.Ctx n} {A x M d y e : Tower.Tm n}
    (hA : Typed objectRules Γ A Package.U0) (hx : Typed objectRules Γ x A)
    (hM : Typed objectRules Γ M (.pi A (.pi (.id (Presentation.rename wk A)
      (Presentation.rename wk x) (.var 0)) Package.U0)))
    (hd : Typed objectRules Γ d (.app (.app M x) (.refl x)))
    (hy : Typed objectRules Γ y A) (he : Typed objectRules Γ e (.id A x y)) :
    Typed objectRules Γ (jApp A x M d y e) (.app (.app M y) e) := by
  have mor : SubstMor objectRules jTelescope Γ
      (consSub e (consSub y (consSub d (consSub M (consSub x (consSub A
        fun i => Fin.elim0 i)))))) := by
    intro i
    refine Fin.cases he (fun i => ?_) i
    refine Fin.cases hy (fun i => ?_) i
    refine Fin.cases hd (fun i => ?_) i
    refine Fin.cases hM (fun i => ?_) i
    refine Fin.cases hx (fun i => ?_) i
    refine Fin.cases hA (fun i => ?_) i
    exact i.elim0
  exact jSpine_typedO.substitute mor

/-- The stage of the numbers and their constructors is inside the object
package. -/
theorem ctorStage_sub_objectRules : RulesSub ctorStage objectRules where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := by
    intro name type declared
    change (if allowedIn [numN, zeroN, sucN] name then allTypes name else none) = some type
      at declared
    by_cases allowed : allowedIn [numN, zeroN, sucN] name = true
    · rw [if_pos allowed] at declared
      have mem : name ∈ [numN, zeroN, sucN] := by simpa [allowedIn] using allowed
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · rw [show objectRules.constantType numN = allTypes numN from rfl]
        exact declared
      · rw [show objectRules.constantType zeroN = allTypes zeroN from rfl]
        exact declared
      · rw [show objectRules.constantType sucN = allTypes sucN from rfl]
        exact declared
    · rw [if_neg allowed] at declared
      cases declared
  computation := fun step => .inl ((stage_sub_rules _).computation step)

theorem numRecConst_typedO {n : Nat} {Γ : Tower.Ctx n} :
    Typed objectRules Γ (.const numRecName) (liftClosed numRecType) :=
  .const (rfl : objectRules.constantType numRecName = some numRecType)
    (Derivable.mono ctorStage_sub_objectRules numRecType_typed) (.sort _)

/-- The telescope `P z s x` of `num-rec`. -/
abbrev numRecTelescope : Tower.Ctx 4 :=
  .snoc (.snoc (.snoc (.snoc .nil (.pi numT Package.U0)) (.app (.var 0) (.const zeroN)))
    (.pi numT (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (.app (.const sucN) (.var 1))))))
    numT

theorem numRecSpine_typedO :
    Typed objectRules numRecTelescope (numRecApp (.var 3) (.var 2) (.var 1) (.var 0))
      (.app (.var 3) (.var 0)) := by
  have r0 : Typed objectRules numRecTelescope (.const numRecName) (liftClosed numRecType) :=
    numRecConst_typedO
  unfold Package.numRecType at r0
  exact .appElim (.appElim (.appElim (.appElim r0 (.var 3)) (.var 2)) (.var 1)) (.var 0)

/-- **The recursor** at a family of the lowest universe:
`num-rec M z s x : M x`. -/
theorem numRec_typedO {n : Nat} {Γ : Tower.Ctx n} {M z s x : Tower.Tm n}
    (hM : Typed objectRules Γ M (.pi numT Package.U0))
    (hz : Typed objectRules Γ z (.app M (.const zeroN)))
    (hs : Typed objectRules Γ s (.pi numT (.pi (.app (Presentation.rename wk M) (.var 0))
      (.app (Presentation.rename wk (Presentation.rename wk M)) (.app (.const sucN) (.var 1))))))
    (hx : Typed objectRules Γ x numT) :
    Typed objectRules Γ (numRecApp M z s x) (.app M x) := by
  have mor : SubstMor objectRules numRecTelescope Γ
      (consSub x (consSub s (consSub z (consSub M fun i => Fin.elim0 i)))) := by
    intro i
    refine Fin.cases hx (fun i => ?_) i
    refine Fin.cases hs (fun i => ?_) i
    refine Fin.cases hz (fun i => ?_) i
    refine Fin.cases hM (fun i => ?_) i
    exact i.elim0
  exact numRecSpine_typedO.substitute mor

/-! ## The published facts, realized in the typed judgment -/

section Realizations

open IdentityEquality.Carriers (substRealizationAt)

/-- A variable of a carrier, seen past one more binder. -/
theorem var_weaken_carrier {n : Nat} {Γ : Tower.Ctx n} {i : Fin n} {τ : HOL.Ty SetBase}
    {X : Tower.Tm n} (h : Typed objectRules Γ (.var i) (setReading.carrierAt n τ)) :
    Typed objectRules (.snoc Γ X) (.var i.succ) (setReading.carrierAt (n + 1) τ) := by
  simpa only [HOLReading.rename_carrierAt, Presentation.rename, wk] using h.weaken (extension := X)

/-- **Reflexivity** at every carrier: `λx. refl x` proves `∀x. x = x` under the
identity reading. -/
theorem reflRealization_typedO (τ : HOL.Ty SetBase) :
    Typed objectRules .nil reflRealization
      (programCodes.holdsOf (setReading.allOf τ (.lam (setReading.eqOf τ (.var 0) (.var 0))))) :=
  setReading_laws.refl_typed τ

/-- The code of `subst@A : ∀P x y. x = y → P x → P y`. -/
def substCodeAt (τ : HOL.Ty SetBase) : Tower.Tm 0 :=
  setReading.allOf (.arr τ .prop) (.lam (setReading.allOf τ (.lam (setReading.allOf τ (.lam
    (programCodes.impOf (setReading.eqOf τ (.var 1) (.var 0))
      (programCodes.impOf (.app (.var 2) (.var 1)) (.app (.var 2) (.var 0)))))))))

/-- **Substitution** at every carrier, by identity elimination at the code
motive `λ y p. holds (P y)`. -/
theorem substRealizationAt_typedO (τ : HOL.Ty SetBase) :
    Typed objectRules .nil (substRealizationAt τ) (programCodes.holdsOf (substCodeAt τ)) := by
  have L := setReading_laws
  let C : (k : Nat) → Tower.Tm k := fun k => setReading.carrierAt k τ
  let Θ1 : Tower.Ctx 1 := .snoc .nil (setReading.carrierAt 0 (.arr τ .prop))
  let Θ2 : Tower.Ctx 2 := .snoc Θ1 (C 1)
  let Θ3 : Tower.Ctx 3 := .snoc Θ2 (C 2)
  let Θ4 : Tower.Ctx 4 := .snoc Θ3 (programCodes.holdsOf (setReading.eqOf τ (.var 1) (.var 0)))
  let Θ5 : Tower.Ctx 5 := .snoc Θ4 (programCodes.holdsOf (.app (.var 3) (.var 2)))
  -- the variables
  have P1 : Typed objectRules Θ1 (.var 0) (setReading.carrierAt 1 (.arr τ .prop)) :=
    setReading.var_carrier (.arr τ .prop)
  have P3 : Typed objectRules Θ3 (.var 2) (setReading.carrierAt 3 (.arr τ .prop)) :=
    var_weaken_carrier (var_weaken_carrier P1)
  have x2 : Typed objectRules Θ2 (.var 0) (C 2) := setReading.var_carrier τ
  have x3 : Typed objectRules Θ3 (.var 1) (C 3) := var_weaken_carrier x2
  have y3 : Typed objectRules Θ3 (.var 0) (C 3) := setReading.var_carrier τ
  have P5 : Typed objectRules Θ5 (.var 4) (setReading.carrierAt 5 (.arr τ .prop)) :=
    var_weaken_carrier (var_weaken_carrier P3)
  have x5 : Typed objectRules Θ5 (.var 3) (C 5) := var_weaken_carrier (var_weaken_carrier x3)
  have y5 : Typed objectRules Θ5 (.var 2) (C 5) := var_weaken_carrier (var_weaken_carrier y3)
  -- the codes
  have eq3 : Typed objectRules Θ3 (setReading.eqOf τ (.var 1) (.var 0)) programCodes.propT :=
    L.eqOf_typed x3 y3
  have imp3 : Typed objectRules Θ3
      (programCodes.impOf (.app (.var 2) (.var 1)) (.app (.var 2) (.var 0))) programCodes.propT :=
    L.impOf_typed (HOLReading.app_carrier (τ := .prop) P3 x3)
      (HOLReading.app_carrier (τ := .prop) P3 y3)
  have body3 : Typed objectRules Θ3 (programCodes.impOf (setReading.eqOf τ (.var 1) (.var 0))
      (programCodes.impOf (.app (.var 2) (.var 1)) (.app (.var 2) (.var 0)))) programCodes.propT :=
    L.impOf_typed eq3 imp3
  have code2 := L.allOf_typed (τ := τ) (.lamIntro (L.pi_typed (L.carrierAt_typed τ) L.prop_typed)
    L.proofs_universe body3)
  have P4 : Typed objectRules Θ4 (.var 3) (setReading.carrierAt 4 (.arr τ .prop)) :=
    var_weaken_carrier P3
  have x4 : Typed objectRules Θ4 (.var 2) (C 4) := var_weaken_carrier x3
  have y4 : Typed objectRules Θ4 (.var 1) (C 4) := var_weaken_carrier y3
  -- the eliminator at the code motive
  have C6 : Presentation.rename wk (C 5) = C 6 := HOLReading.rename_carrierAt _ _ _
  have motiveBody : Typed objectRules
      (.snoc (.snoc Θ5 (C 5)) (.id (C 6) (.var 4) (.var 0)))
      (programCodes.holdsOf (.app (.var 6) (.var 1))) Package.U0 := by
    have P7 : Typed objectRules (.snoc (.snoc Θ5 (C 5)) (.id (C 6) (.var 4) (.var 0))) (.var 6)
        (setReading.carrierAt 7 (.arr τ .prop)) := var_weaken_carrier (var_weaken_carrier P5)
    have y7 : Typed objectRules (.snoc (.snoc Θ5 (C 5)) (.id (C 6) (.var 4) (.var 0))) (.var 1)
        (C 7) := var_weaken_carrier (setReading.var_carrier τ)
    exact L.holdsOf_typed (HOLReading.app_carrier (τ := .prop) P7 y7)
  have x6 : Typed objectRules (.snoc Θ5 (C 5)) (.var 4) (C 6) := var_weaken_carrier x5
  have y6 : Typed objectRules (.snoc Θ5 (C 5)) (.var 0) (C 6) := setReading.var_carrier τ
  have formed₂ : Typed objectRules (.snoc Θ5 (C 5))
      (.pi (.id (C 6) (.var 4) (.var 0)) Package.U0)
      U1 :=
    piO (raiseO (.idForm (L.carrierAt_typed τ) (.sort _) x6 y6)) U0_typedO
  have formed : Typed objectRules Θ5 (.pi (C 5) (.pi (.id (C 6) (.var 4) (.var 0)) Package.U0))
      U1 :=
    piO (raiseO (L.carrierAt_typed τ)) formed₂
  have motive : Typed objectRules Θ5 substMotive
      (.pi (C 5) (.pi (.id (C 6) (.var 4) (.var 0)) Package.U0)) :=
    .lamIntro formed (.sort _) (.lamIntro formed₂ (.sort _) motiveBody)
  have reflAt : Typed objectRules Θ5 (.refl (.var 3))
      (inst0 (.var 3) (.id (C 6) (.var 4) (.var 0))) := by
    have h : inst0 (.var 3) (.id (C 6) (.var 4) (.var 0)) = .id (C 5) (.var 3) (.var 3) := by
      simp only [inst0, Presentation.subst, C, HOLReading.subst_carrierAt]
      rfl
    rw [h]
    exact .reflIntro x5
  have method : Typed objectRules Θ5 (.var 0)
      (.app (.app substMotive (.var 3)) (.refl (.var 3))) :=
    .conv (.var 0) (.symm (betaTwoT formed (.sort _) formed₂ motiveBody x5 reflAt)) (.sort _)
  have path : Typed objectRules Θ5 (.var 1) (.id (C 5) (.var 3) (.var 2)) :=
    .conv (.var 1) (L.equal_holds_eq x5 y5) (.sort _)
  have pathAt : Typed objectRules Θ5 (.var 1) (inst0 (.var 2) (.id (C 6) (.var 4) (.var 0))) := by
    have h : inst0 (.var 2) (.id (C 6) (.var 4) (.var 0)) = .id (C 5) (.var 3) (.var 2) := by
      simp only [inst0, Presentation.subst, C, HOLReading.subst_carrierAt]
      rfl
    rw [h]
    exact path
  have eliminated := j_typedO (L.carrierAt_typed τ) x5 (by rw [C6]; exact motive) method y5 path
  have body5 : Typed objectRules Θ5 (jApp (C 5) (.var 3) substMotive (.var 0) (.var 2) (.var 1))
      (programCodes.holdsOf (.app (.var 4) (.var 2))) :=
    .conv eliminated (betaTwoT formed (.sort _) formed₂ motiveBody y5 pathAt) (.sort _)
  have body4 : Typed objectRules Θ4
      (.lam (jApp (C 5) (.var 3) substMotive (.var 0) (.var 2) (.var 1)))
      (programCodes.holdsOf
        (programCodes.impOf (.app (.var 3) (.var 2)) (.app (.var 3) (.var 1)))) :=
    L.impIntro (HOLReading.app_carrier (τ := .prop) P4 x4)
      (HOLReading.app_carrier (τ := .prop) P4 y4) body5
  have body3' := L.impIntro eq3 imp3 body4
  have body2' := L.allIntro (τ := τ) body3 body3'
  have body1' := L.allIntro (τ := τ) code2 body2'
  have realized := L.allIntro (τ := .arr τ .prop)
    (L.allOf_typed (τ := τ) (.lamIntro (L.pi_typed (L.carrierAt_typed τ) L.prop_typed)
      L.proofs_universe code2)) body1'
  have spelled : (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
      (Presentation.rename wk (Presentation.rename wk
        (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 τ))))) : Tower.Tm 5) =
      FormationSensitiveHOLInterface.typeAt SetProfile.types 5 τ := by
    simp only [FormationSensitiveHOLInterface.typeAt_rename]
  have carrier5 :
      (FormationSensitiveHOLInterface.typeAt SetProfile.types 5 τ : Tower.Tm 5) = C 5 :=
    (setReading_carrierAt τ).symm
  unfold substRealizationAt
  rw [show (IdentityEquality.Carriers.carrier τ : Tower.Tm 5) = C 5 from carrier5]
  exact realized

/-- **Induction** on the numbers, by the recursor at the code motive
`λ m. holds (P m)`. -/
theorem inductionRealization_typedO :
    Typed objectRules .nil inductionRealization
      (programCodes.holdsOf SetProfile.inductionCode) := by
  have L := setReading_laws
  let I1 : Tower.Ctx 1 := .snoc .nil (setReading.carrierAt 0 (.arr numTy .prop))
  let step2 : Tower.Tm 2 := setReading.allOf numTy
    (.lam (programCodes.impOf (.app (.var 2) (.var 0))
    (.app (.var 2) (.app (.const sucN) (.var 0)))))
  let I2 : Tower.Ctx 2 := .snoc I1 (programCodes.holdsOf (.app (.var 0) (.const zeroN)))
  let I3 : Tower.Ctx 3 := .snoc I2 (programCodes.holdsOf step2)
  let I4 : Tower.Ctx 4 := .snoc I3 (setReading.carrierAt 3 numTy)
  have P1 : Typed objectRules I1 (.var 0) (.pi numT (.const propN)) :=
    setReading.var_carrier (.arr numTy .prop)
  have P2 : Typed objectRules I2 (.var 1) (.pi numT (.const propN)) := P1.weaken
  have P3 : Typed objectRules I3 (.var 2) (.pi numT (.const propN)) := P2.weaken
  have P4 : Typed objectRules I4 (.var 3) (.pi numT (.const propN)) := P3.weaken
  -- codes
  have atZero1 : Typed objectRules I1 (.app (.var 0) (.const zeroN)) (.const propN) :=
    .appElim P1 zero_typedO
  have S1 : Typed objectRules I1 (setReading.allOf numTy (.lam (programCodes.impOf
      (.app (.var 1) (.var 0)) (.app (.var 1) (.app (.const sucN) (.var 0)))))) (.const propN) := by
    have hP : Typed objectRules (.snoc I1 numT) (.var 1) (.pi numT (.const propN)) := P1.weaken
    exact L.allOf_typed (τ := numTy) (.lamIntro (piO num_typedO prop_typedO) (.sort _)
      (L.impOf_typed (.appElim hP (.var 0)) (.appElim hP (.appElim suc_typedO (.var 0)))))
  have A1 : Typed objectRules I1 (setReading.allOf numTy (.lam (.app (.var 1) (.var 0))))
      (.const propN) := by
    have hP : Typed objectRules (.snoc I1 numT) (.var 1) (.pi numT (.const propN)) := P1.weaken
    exact L.allOf_typed (τ := numTy) (.lamIntro (piO num_typedO prop_typedO) (.sort _)
      (.appElim hP (.var 0)))
  have step2_typed : Typed objectRules I2 step2 (.const propN) := by
    have hP' : Typed objectRules (.snoc I2 numT) (.var 2) (.pi numT (.const propN)) := P2.weaken
    exact L.allOf_typed (τ := numTy) (.lamIntro (piO num_typedO prop_typedO) (.sort _)
      (L.impOf_typed (.appElim hP' (.var 0)) (.appElim hP' (.appElim suc_typedO (.var 0)))))
  have A2 : Typed objectRules I2 (setReading.allOf numTy (.lam (.app (.var 2) (.var 0))))
      (.const propN) := by
    have hP' : Typed objectRules (.snoc I2 numT) (.var 2) (.pi numT (.const propN)) := P2.weaken
    exact L.allOf_typed (τ := numTy) (.lamIntro (piO num_typedO prop_typedO) (.sort _)
      (.appElim hP' (.var 0)))
  -- the motive `λ m. holds (P m)`
  have motiveBody : Typed objectRules (.snoc I4 numT)
      (programCodes.holdsOf (.app (.var 4) (.var 0))) Package.U0 :=
    L.holdsOf_typed (.appElim (P4.weaken : Typed objectRules (.snoc I4 numT) (.var 4)
      (.pi numT (.const propN))) (.var 0))
  have motiveFormed : Typed objectRules I4 (.pi numT Package.U0) U1 :=
    piO (raiseO num_typedO) U0_typedO
  have motive : Typed objectRules I4 inductionMotive (.pi numT Package.U0) :=
    .lamIntro motiveFormed (.sort _) motiveBody
  -- the base
  have base : Typed objectRules I4 (.var 2) (.app inductionMotive (.const zeroN)) :=
    .conv (.var 2) (.symm (Derivable.betaPi motiveFormed (.sort _) motiveBody zero_typedO))
      (.sort _)
  -- the step, decoded
  let I5 : Tower.Ctx 5 := .snoc I4 numT
  have P5 : Typed objectRules I5 (.var 4) (.pi numT (.const propN)) := P4.weaken
  have atVar : Typed objectRules I5 (.app (.var 4) (.var 0)) (.const propN) :=
    .appElim P5 (.var 0)
  have atSuc : Typed objectRules I5 (.app (.var 4) (.app (.const sucN) (.var 0))) (.const propN) :=
    .appElim P5 (.appElim suc_typedO (.var 0))
  have shiftedBody : Typed objectRules (.snoc I5 numT)
      (programCodes.holdsOf (.app (.var 5) (.var 0))) Package.U0 :=
    L.holdsOf_typed (.appElim (P5.weaken : Typed objectRules (.snoc I5 numT) (.var 5)
      (.pi numT (.const propN))) (.var 0))
  let I6 : Tower.Ctx 6 := .snoc I5 (programCodes.holdsOf (.app (.var 4) (.var 0)))
  have P6 : Typed objectRules I6 (.var 5) (.pi numT (.const propN)) := P5.weaken
  have shiftedBody₂ : Typed objectRules (.snoc I6 numT)
      (programCodes.holdsOf (.app (.var 6) (.var 0))) Package.U0 :=
    L.holdsOf_typed (.appElim (P6.weaken : Typed objectRules (.snoc I6 numT) (.var 6)
      (.pi numT (.const propN))) (.var 0))
  have hypothesisEq : Equal objectRules I5 (programCodes.holdsOf (.app (.var 4) (.var 0)))
      (.app (Presentation.rename wk inductionMotive) (.var 0)) Package.U0 :=
    .symm (Derivable.betaPi (piO (raiseO num_typedO) U0_typedO) (.sort _) shiftedBody (.var 0))
  have conclusionEq : Equal objectRules I6
      (programCodes.holdsOf (.app (.var 5) (.app (.const sucN) (.var 1))))
      (.app (Presentation.rename wk (Presentation.rename wk inductionMotive))
        (.app (.const sucN) (.var 1))) Package.U0 :=
    .symm (Derivable.betaPi (piO (raiseO num_typedO) U0_typedO) (.sort _) shiftedBody₂
      (.appElim suc_typedO (.var 1)))
  have stepEq : Equal objectRules I4
      (programCodes.holdsOf (setReading.allOf numTy
        (.lam (programCodes.impOf (.app (.var 4) (.var 0))
        (.app (.var 4) (.app (.const sucN) (.var 0)))))))
      (.pi numT (.pi (.app (Presentation.rename wk inductionMotive) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk inductionMotive))
          (.app (.const sucN) (.var 1))))) Package.U0 :=
    .trans (L.equal_holds_all_lam (L.impOf_typed atVar atSuc))
      (L.equal_pi (.refl (L.carrierAt_typed numTy))
        (.trans (L.equal_holds_imp atVar atSuc) (L.equal_pi hypothesisEq conclusionEq)))
  have step : Typed objectRules I4 (.var 1)
      (.pi numT (.pi (.app (Presentation.rename wk inductionMotive) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk inductionMotive))
          (.app (.const sucN) (.var 1))))) :=
    .conv (.var 1) stepEq (.sort _)
  have recursed := numRec_typedO motive base step (.var 0)
  have body4 : Typed objectRules I4 (numRecApp inductionMotive (.var 2) (.var 1) (.var 0))
      (programCodes.holdsOf (.app (.var 3) (.var 0))) :=
    .conv recursed (Derivable.betaPi motiveFormed (.sort _) motiveBody (.var 0)) (.sort _)
  have hB4 : Typed objectRules I4 (.app (.var 3) (.var 0)) (.const propN) := .appElim P4 (.var 0)
  have body3 := L.allIntro (τ := numTy) hB4 body4
  have body2 := L.impIntro step2_typed A2 body3
  have body1 := L.impIntro atZero1 (L.impOf_typed S1 A1) body2
  exact L.allIntro (τ := .arr numTy .prop) (L.impOf_typed atZero1 (L.impOf_typed S1 A1)) body1

end Realizations

/-! ## `Falsum` published by name -/

section Defined

/-- The name of the signature's defined constant. -/
abbrev falsumN : DeclName := SetProfile.constantName .falsum

/-- The object package with `Falsum := ∀p. p` published by name: `Falsum` is a
constant of `prop` whose δ-rule steps to `botCode`. -/
abbrev definedRules : Rules Tower.Head := objectRules.withTheorem falsumN (.const propN) botCode

theorem falsumN_fresh : objectRules.constantType falsumN = none := by decide

theorem prop_isType : IsType objectRules .nil (.const propN) := ⟨_, .sort _, prop_typedO⟩

/-- **`Falsum` is a term of `prop`** in the extended package. -/
theorem falsum_typed : Typed definedRules .nil (.const falsumN) (.const propN) :=
  withTheorem_typed falsumN_fresh prop_isType

/-- **`Falsum` is equal to its body**, `botCode`, by its δ-step. -/
theorem falsum_equal_bot : Equal definedRules .nil (.const falsumN) botCode (.const propN) :=
  withTheorem_equal_body falsumN_fresh prop_isType botCode_typed

/-- The object package is included in the extended package. -/
theorem objectRules_defined : objectRules.Morphism definedRules (fun head => head) where
  headTyping := fun typing => typing
  isUniverse := fun isU => isU
  join := fun join => join
  cumulative := fun order => order
  headEq := fun equality => equality
  constantType := by
    intro name type declared
    simpa only [Tm.mapHead_id] using (withTheorem_sub (T := .const propN) (body := botCode)
      falsumN_fresh).constantType declared
  computation := by
    intro n left right step
    simpa only [Tm.mapHead_id] using (withTheorem_sub (T := .const propN) (body := botCode)
      falsumN_fresh).computation step

/-- The constants of the set profile the extended package reads: those of the
set reading, and `Falsum` by its name. -/
def definedConstant : {τ : HOL.Ty SetBase} → SetConst τ → Option (Tower.Tm 0)
  | _, .falsum => some (.const falsumN)
  | _, c => setConstant c

/-- The set profile with `Falsum` defined, read in the extended package: the
base carries the δ-rule of the definition. -/
def definedReading : HOLReading Tower.Head SetBase SetConst :=
  { setReading with
    base := rules.withTheorem falsumN (.const propN) botCode
    constant := definedConstant }

/-- **The reading's package is the extended package.** -/
theorem definedReading_rules : definedReading.rules = definedRules := by
  have codeFree : programCodes.codeType falsumN = none := by decide
  change programCodes.extend (rules.withTheorem falsumN (.const propN) botCode) =
    objectRules.withTheorem falsumN (.const propN) botCode
  simp only [Codes.extend, Rules.withTheorem]
  congr 1
  · funext c
    by_cases same : c = falsumN
    · subst same
      simp [codeFree]
    · simp [same]
  · simp only [Normalization.RootComputation.union]
    congr 1
    funext n l r
    exact propext or_right_comm

theorem typed_defined {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (typed : Typed objectRules Γ t A) : Typed definedReading.rules Γ t A :=
  definedReading_rules ▸ typed.of_morphism objectRules_defined

theorem definedReading_carrierAt {n : Nat} (τ : HOL.Ty SetBase) :
    definedReading.carrierAt n τ = setReading.carrierAt n τ := by
  induction τ generalizing n with
  | prop => rfl
  | base b => rfl
  | arr a b ia ib => simp only [HOLReading.carrierAt, ia, ib]

/-- **The reading with the definition extends the set reading**: it reads every
term the set reading reads, as the set reading reads it. -/
theorem definedReading_term_of_setReading :
    ∀ {Γ : HOL.Ctx SetBase} {τ : HOL.Ty SetBase} {t : HOL.Term SetConst Γ τ}
      {out : Tower.Tm Γ.length}, setReading.term t = some out → definedReading.term t = some out
  | _, _, .var _, _, read => read
  | _, _, .const c, _, read => by
      cases c
      case falsum => cases read
      all_goals exact read
  | _, _, .app f a, _, read => by
      obtain ⟨f', a', hf, ha, rfl⟩ := HOLReading.term_app read
      simp only [HOLReading.term, definedReading_term_of_setReading hf,
        definedReading_term_of_setReading ha]
      rfl
  | _, _, .lam b, _, read => by
      obtain ⟨b', hb, rfl⟩ := HOLReading.term_lam read
      simp only [HOLReading.term, definedReading_term_of_setReading hb]
      rfl
  | _, _, .imp p q, _, read => by
      obtain ⟨p', q', hp, hq, rfl⟩ := HOLReading.term_imp read
      simp only [HOLReading.term, definedReading_term_of_setReading hp,
        definedReading_term_of_setReading hq]
      rfl
  | _, _, .all b, _, read => by
      obtain ⟨b', hb, rfl⟩ := HOLReading.term_all read
      simp only [HOLReading.term, definedReading_term_of_setReading hb]
      rfl
  | _, _, .eq l r, _, read => by
      obtain ⟨l', r', hl, hr, rfl⟩ := HOLReading.term_eq read
      simp only [HOLReading.term, definedReading_term_of_setReading hl,
        definedReading_term_of_setReading hr]
      rfl
  | _, _, .top, _, read | _, _, .bot, _, read | _, _, .and _ _, _, read
  | _, _, .or _ _, _, read | _, _, .not _, _, read | _, _, .ex _, _, read => by cases read

/-- **The reading with `Falsum` defined satisfies the laws of a reading.** Every
law is the law of the set reading, carried along the extension, and `Falsum` is
a term of `prop`. -/
theorem definedReading_laws : definedReading.Laws where
  quantifier τ := by
    rw [show definedReading.carrier τ = setReading.carrier τ from definedReading_carrierAt τ]
    exact setReading_laws.quantifier τ
  equation τ := by
    rw [show definedReading.carrier τ = setReading.carrier τ from definedReading_carrierAt τ]
    exact setReading_laws.equation τ
  allName_apart := setReading_laws.allName_apart
  eqName_apart := setReading_laws.eqName_apart
  imp_apart := setReading_laws.imp_apart
  holds_apart := setReading_laws.holds_apart
  proofs_universe := setReading_laws.proofs_universe
  proofs_typed := setReading_laws.proofs_typed
  proofs_pi := setReading_laws.proofs_pi
  holds_formed := by
    obtain ⟨w, hw, typed⟩ := setReading_laws.holds_formed
    exact ⟨w, hw, typed_defined typed⟩
  sort_typed b := typed_defined (setReading_laws.sort_typed b)
  const_typed c t found := by
    cases c <;> simp only [definedReading, definedConstant, setConstant, reduceCtorEq,
      Option.some.injEq] at found <;> subst found <;>
      first
        | exact definedReading_rules ▸ falsum_typed
        | exact typed_defined zero_typedO
        | exact typed_defined suc_typedO
        | exact typed_defined add_typedO
        | exact typed_defined power_typedO
        | exact typed_defined pow_typedO

/-- **The definition of `Falsum` is realized by its δ-step**, and the equations
of `add` and `pow` by the root steps of the executable package, as in the set
reading. -/
theorem definedReading_realizes : definedReading.Realizes SetProfile.definedEquations := by
  intro equation mem
  rcases List.mem_cons.mp mem with rfl | mem
  · refine ⟨_, _, rfl, rfl, fun (σ : Sub Tower.Head 0 _) => ?_⟩
    change (rules.withTheorem falsumN (.const propN) botCode).computation.step
      (.const falsumN) (Presentation.subst σ botCode)
    rw [Normalization.subst_closed σ botCode]
    exact withTheorem_delta
  · have realized := setReading_realizes equation mem
    simp only [SetProfile.sourceEquations, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl <;>
      obtain ⟨l, r, hl, hr, roots⟩ := realized <;>
      exact ⟨l, r, hl, hr, fun σ => .inl (roots σ)⟩

end Defined

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
