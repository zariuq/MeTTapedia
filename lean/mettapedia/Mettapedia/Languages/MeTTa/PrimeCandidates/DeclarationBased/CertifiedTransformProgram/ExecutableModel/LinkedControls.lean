import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LinkedProofs
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.HostedTransport

/-!
# Controls for the linked proofs, in the selected typed judgment

The controls of the identity profile (`IdentityEquality.HostedTransport`,
`IdentityEquality.Controls`) are stated for the formation-sensitive judgment.
Here they are restated for the selected typed judgment.

* **Wrong index** (object package). At every numeral `m` the linked `zero-add`
  proof is evidence for `Id num (add zero m) m` (`linkedZeroAdd_numeral_typedO`),
  and no closed term is evidence for `Id num (add zero m) (m + 1)`
  (`add_zero_wrong_index`); in particular neither the linked transport
  construction (`closedIdentity_wrong_indexO`) nor reflexivity at `zero`
  (`reflRealization_wrong_indexO`) proves a wrong index. The refutations come
  from the consistency model: identity evidence between numerals relates equal
  numbers.
* **An equation code without its decoding is not an identity type** (object
  package). Under the identity reading, `holds (eq@num x y)` is `Id num x y`
  (`holdsEq_identityO`). A code-valued variable `e : num → num → prop` stands
  for the source's equality without its decoding rule, and `holds (e x y)` is
  not `Id num x y` (`holdsEq_not_identityO`): the identification is the
  reading's decoding step, not a property of codes.
* **Reflexivity is not evidence at an open index** (executable package). No
  reflexivity proof has the type `Id num (add zero k) k` at an open index `k`
  in the selected judgment of the executable package `rules`
  (`refl_not_hosted_open_rules`), by the normalization model of that package:
  identity types are injective and `add zero k` and `k` are distinct neutral
  terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency (Truth Read DataEq World numClass
  numClass_injective dataValue no_closed_proof)
open Mettapedia.Logic
open SetProfile (numTy zeroNative sucNative addNative)
open IdentityEquality.Translation (linkedZeroAdd)
open IdentityEquality.Realizations (reflRealization)
open CertifiedTransformProgram.Execution (numeral)
open Package (numT)

namespace CodeModel

/-! ## Numerals -/

theorem numeral_typedO {n : Nat} {Γ : Tower.Ctx n} :
    ∀ m : Nat, Typed objectRules Γ (numeral m) numT
  | 0 => zero_typedO
  | m + 1 => .appElim suc_typedO (numeral_typedO m)

/-- `add zero a : num`. -/
theorem addZero_typedO {n : Nat} {Γ : Tower.Ctx n} {a : Tower.Tm n}
    (ha : Typed objectRules Γ a numT) : Typed objectRules Γ (addNative zeroNative a) numT := by
  have applied : Typed objectRules Γ (.app (.const addN) zeroNative) (.pi numT numT) :=
    .appElim add_typedO zero_typedO
  exact .appElim applied ha

/-- The numerals of the program are the numerals of the consistency model. -/
theorem numeral_model (v : Nat → Nat) :
    ∀ m : Nat, (numeral m : Tower.Tm 0) = Consistency.numeral (model v).toSetting m
  | 0 => rfl
  | m + 1 => by
      change sucNative (numeral m) = .app (.const sucN) (Consistency.numeral _ m)
      rw [numeral_model v m]
      rfl

/-- The value of a numeral in the consistency model is its number. -/
theorem dataValue_numeral (v : Nat → Nat) :
    ∀ (m : Nat) (related : DataEq (model v).toSetting.numerals .num
      (Consistency.numeral (model v).toSetting m : Tower.Tm 0)
      (Consistency.numeral (model v).toSetting m)),
      dataValue (P := Prop) (model v).toSetting.numerals .num _ related =
        numClass (model v).toSetting.numerals m
  | 0, _ => rfl
  | m + 1, related => by
      have inner : DataEq (model v).toSetting.numerals .num
          (Consistency.numeral (model v).toSetting m : Tower.Tm 0)
          (Consistency.numeral (model v).toSetting m) := DataEq.numeral m
      calc dataValue (P := Prop) (model v).toSetting.numerals .num _ related
          = Consistency.sucClass (model v).toSetting.numerals
              (dataValue (P := Prop) (model v).toSetting.numerals .num _ inner) :=
            Consistency.dataValue_suc inner related
        _ = Consistency.sucClass (model v).toSetting.numerals
              (numClass (model v).toSetting.numerals m) := by rw [dataValue_numeral v m inner]
        _ = numClass (model v).toSetting.numerals (m + 1) := rfl

/-! ## Wrong index -/

/-- **No identity evidence between different numerals.** No closed term of the
object package proves `Id num j k` for numerals `j ≠ k`. -/
theorem numeral_identity_apart {j k : Nat} (apart : j ≠ k) (t : Tower.Tm 0) :
    ¬ Typed objectRules .nil t (.id numT (numeral j) (numeral k)) := by
  intro typed
  have coded : Typed objectRules .nil t
      (programCodes.holdsOf (setReading.eqOf numTy (numeral j) (numeral k))) :=
    .conv typed (.symm (setReading_laws.equal_holds_eq (numeral_typedO j) (numeral_typedO k)))
      (.sort _)
  have eqNum : (model fun _ => 0).reading.eqCarrier eqNumN = some ⟨.data, .num⟩ := by
    change (SetProfile.eqInstance? (SetProfile.eqName SetProfile.numTy)).map carrierOf = _
    rw [SetProfile.eqInstance?_eqName]
    rfl
  have truth : Truth (model fun _ => 0).reading World.closed
      (setReading.eqOf numTy (numeral j) (numeral k))
      (numClass (model fun _ => 0).toSetting.numerals j =
        numClass (model fun _ => 0).toSetting.numerals k) := by
    rw [numeral_model (fun _ => 0) j, numeral_model (fun _ => 0) k,
      ← dataValue_numeral (fun _ => 0) j (DataEq.numeral j),
      ← dataValue_numeral (fun _ => 0) k (DataEq.numeral k)]
    exact Truth.eq eqNum .refl (.data (DataEq.numeral j)) (.data (DataEq.numeral k))
  exact no_closed_proof (objectSound fun _ => 0) truth
    (fun same => apart (numClass_injective (model_laws fun _ => 0).truth.numerals same)) t coded

/-- `add zero m` computes to `m` in the typed equality of the object package. -/
theorem add_zero_numeral_equal :
    ∀ m : Nat, Equal objectRules .nil (addNative zeroNative (numeral m)) (numeral m) numT
  | 0 => by
      have step : objectRules.computation.step (addNative zeroNative (numeral 0) : Tower.Tm 0)
          (numeral 0) :=
        .inl (rules_step (listed 1 (by decide))
          ⟨zeroN, [], consSub (.const zeroN) (consSub zeroNative fun i => Fin.elim0 i), [],
            mem_zero, rfl, rfl, rfl⟩)
      exact .root step (addZero_typedO zero_typedO) zero_typedO
  | m + 1 => by
      have step : objectRules.computation.step (addNative zeroNative (numeral (m + 1)) : Tower.Tm 0)
          (sucNative (addNative zeroNative (numeral m))) :=
        .inl (rules_step (listed 1 (by decide))
          ⟨sucN, [.recursive],
            consSub (sucNative (numeral m)) (consSub zeroNative fun i => Fin.elim0 i),
            [numeral m], mem_suc, rfl, rfl, rfl⟩)
      exact .trans (.root step (addZero_typedO (numeral_typedO (m + 1)))
          (.appElim suc_typedO (addZero_typedO (numeral_typedO m))))
        (.appCong (.refl suc_typedO) (add_zero_numeral_equal m))

/-- **Wrong index.** No closed term of the object package proves
`Id num (add zero m) (m + 1)`. -/
theorem add_zero_wrong_index (m : Nat) (t : Tower.Tm 0) :
    ¬ Typed objectRules .nil t (.id numT (addNative zeroNative (numeral m)) (numeral (m + 1))) :=
  fun typed => numeral_identity_apart (Nat.succ_ne_self m).symm t
    (.conv typed (.idCong (.refl num_typedO) (.sort _) (add_zero_numeral_equal m)
      (.refl (numeral_typedO (m + 1)))) (.sort _))

/-- **Positive twin.** At every numeral `m`, the linked `zero-add` proof is
evidence for `Id num (add zero m) m` in the object package. -/
theorem linkedZeroAdd_numeral_typedO (m : Nat) :
    Typed objectRules .nil (.app linkedZeroAdd (numeral m))
      (.id numT (addNative zeroNative (numeral m)) (numeral m)) := by
  have L := setReading_laws
  have index : Typed objectRules (.snoc .nil (setReading.carrierAt 0 numTy)) (.var 0) numT := .var 0
  have body : Typed objectRules (.snoc .nil (setReading.carrierAt 0 numTy))
      (setReading.eqOf numTy (addNative zeroNative (.var 0)) (.var 0)) (.const propN) :=
    L.eqOf_typed (τ := numTy) (addZero_typedO index) index
  have applied := L.allElim body linkedZeroAdd_typedO (numeral_typedO m)
  exact .conv applied (L.equal_holds_eq (τ := numTy)
    (addZero_typedO (numeral_typedO m)) (numeral_typedO m)) (.sort _)

/-- The linked construction of the hosted transport, at the numeral `m`, is not
evidence that `add zero m` is `m + 1`. -/
theorem closedIdentity_wrong_indexO (count : Nat) :
    ¬ Typed objectRules .nil (IdentityEquality.HostedTransport.closedIdentity count)
      (.id numT (addNative zeroNative (numeral count)) (numeral (count + 1))) :=
  add_zero_wrong_index count _

/-- Reflexivity at `zero` proves `Id num zero zero`. -/
theorem reflRealization_zero_typedO :
    Typed objectRules .nil (.app reflRealization zeroNative) (.id numT zeroNative zeroNative) :=
  .conv (setReading_laws.allElim (τ := numTy)
      (setReading_laws.eqOf_typed (setReading.var_carrier numTy) (setReading.var_carrier numTy))
      (reflRealization_typedO numTy) zero_typedO)
    (setReading_laws.equal_holds_eq (τ := numTy) zero_typedO zero_typedO) (.sort _)

/-- Reflexivity at `zero` is not evidence that `zero` is one. -/
theorem reflRealization_wrong_indexO :
    ¬ Typed objectRules .nil (.app reflRealization zeroNative) (.id numT zeroNative (numeral 1)) :=
  numeral_identity_apart (j := 0) (k := 1) (by decide) _

/-! ## Equality codes and identity -/

/-- The context `e : num → num → prop, x y : num`: an uninterpreted equation
code and two points. -/
abbrev equationCtx : Tower.Ctx 3 :=
  .snoc (.snoc (.snoc .nil (.pi numT (.pi numT (.const propN)))) numT) numT

/-- Under the identity reading the equation code decodes to the identity type. -/
theorem holdsEq_identityO {n : Nat} {Γ : Tower.Ctx n} {x y : Tower.Tm n}
    (hx : Typed objectRules Γ x numT) (hy : Typed objectRules Γ y numT) :
    Equal objectRules Γ (programCodes.holdsOf (setReading.eqOf numTy x y)) (.id numT x y)
      Package.U0 :=
  setReading_laws.equal_holds_eq hx hy

/-- **An equation code without its decoding is not an identity type.** For an
uninterpreted code-valued `e`, `holds (e x y)` and `Id num x y` are not equal
types: instantiated at `e := λ_ _. ∀p. p` and `x = y = zero`, reflexivity would
prove `∀p. p`. -/
theorem holdsEq_not_identityO :
    ¬ Equal objectRules equationCtx (programCodes.holdsOf (.app (.app (.var 2) (.var 1)) (.var 0)))
      (.id numT (.var 1) (.var 0)) Package.U0 := by
  intro equal
  let falsity : Tower.Tm 0 := .lam (.lam botCode)
  have falsityTyped : Typed objectRules .nil falsity (.pi numT (.pi numT (.const propN))) :=
    .lamIntro (piO num_typedO (piO num_typedO prop_typedO)) (.sort _)
      (.lamIntro (piO num_typedO prop_typedO) (.sort _) botCode_typed)
  have mor : SubstMor objectRules equationCtx .nil
      (consSub zeroNative (consSub zeroNative (consSub falsity fun i => Fin.elim0 i))) := by
    intro i
    refine Fin.cases zero_typedO (fun i => ?_) i
    refine Fin.cases zero_typedO (fun i => ?_) i
    refine Fin.cases falsityTyped (fun i => ?_) i
    exact i.elim0
  have closed := equal.substitute mor
  have inhabited : Typed objectRules .nil (.refl zeroNative)
      (programCodes.holdsOf (.app (.app falsity zeroNative) zeroNative)) :=
    .conv (.reflIntro zero_typedO) (.symm closed) (.sort _)
  have first : Equal objectRules .nil (.app falsity zeroNative) (.lam botCode)
      (.pi numT (.const propN)) :=
    Derivable.betaPi (piO num_typedO (piO num_typedO prop_typedO)) (.sort _)
      (.lamIntro (piO num_typedO prop_typedO) (.sort _) botCode_typed) zero_typedO
  have second : Equal objectRules .nil (.app (.lam botCode) zeroNative) botCode (.const propN) :=
    Derivable.betaPi (piO num_typedO prop_typedO) (.sort _) botCode_typed zero_typedO
  have reduced : Equal objectRules .nil (.app (.app falsity zeroNative) zeroNative) botCode
      (.const propN) :=
    .trans (.appCong first (.refl zero_typedO)) second
  exact consistent_bot (.refl zeroNative)
    (.conv inhabited (setReading_laws.equal_holdsOf reduced) (.sort _))

end CodeModel

/-! ## Reflexivity at an open index, in the executable package -/

section OpenIndex

/-- The context `k : num`. -/
abbrev openIndexCtx : Tower.Ctx 1 := .snoc .nil numT

theorem openIndexCtx_formed : CtxFormed rules openIndexCtx := by
  have numMem : numN ∈ [numN] := List.mem_cons_self ..
  exact .snoc .nil ⟨_, .sort _, Derivable.mono (stage_sub_rules _)
    (numT_typed (Γ := .nil) numMem)⟩

theorem addZeroVar_typed : Typed rules openIndexCtx (addNative zeroNative (.var 0)) numT := by
  have numMem : numN ∈ [numN, zeroN, sucN, addN] := by simp
  have zeroMem : zeroN ∈ [numN, zeroN, sucN, addN] := by simp
  have addMem : addN ∈ [numN, zeroN, sucN, addN] := by simp
  exact Derivable.mono (stage_sub_rules _)
    (addApp_typed numMem addMem (zero_typed numMem zeroMem) (.var 0))

/-- **`add zero k` is not `k` at an open index**, in the typed equality of the
executable package: both are neutral, and the algorithmic comparison of their
spines, which is complete for the package, has no rule for a variable against
an application. -/
theorem addZero_ne_var :
    ¬ Equal rules openIndexCtx (addNative zeroNative (.var 0)) (.var 0) numT := by
  intro equal
  have algorithmicLaws : (algorithmicSetting (setting fun _ => 0)).E.Laws
      (algorithmicSetting (setting fun _ => 0)).R (algorithmicSetting (setting fun _ => 0)).roles :=
    algorithmicSetting_laws (S := setting fun _ => 0) (laws _) (constants _) roots heads algebra
  obtain ⟨reducible, related⟩ := Equal.reducible (S := algorithmicSetting (setting fun _ => 0))
    algorithmicLaws algorithmicConstants equal openIndexCtx_formed
  obtain ⟨fieldPack, same, _⟩ :=
    Reducible.inductive_view (S := algorithmicSetting (setting fun _ => 0))
    (T := numN) (ctors := ctors) roles_num reducible
  rw [same] at related
  obtain ⟨red, red', _, normal⟩ := related
  have addNeutral : Neutral (algorithmicSetting (setting fun _ => 0)).roles
      (addNative zeroNative (.var 0) : Tower.Tm 1) :=
    Neutral.stuck_single (c := addN) (before := [zeroNative]) (after := []) roles_add rfl (.var 0)
  have varNeutral : Neutral (algorithmicSetting (setting fun _ => 0)).roles (.var 0 : Tower.Tm 1) :=
    .var 0
  cases normal with
  | ctor mem _ =>
      have back :=
        WhRed.eq_of_whnf (varNeutral.whnf (algorithmicSetting (setting fun _ => 0)).shape) red'.red
      exact appSpine_const_ne_var back
  | neutral _ _ conv =>
      obtain rfl :=
        WhRed.eq_of_whnf (addNeutral.whnf (algorithmicSetting (setting fun _ => 0)).shape) red.red
      obtain rfl :=
        WhRed.eq_of_whnf (varNeutral.whnf (algorithmicSetting (setting fun _ => 0)).shape) red'.red
      obtain ⟨U, spines, _⟩ := conv.2 (ρ := idRen) (fun i => (rename_id _).symm)
        openIndexCtx_formed
      simp only [rename_id] at spines
      cases spines

/-- **Reflexivity is not evidence at an open index.** In the executable
package, no reflexivity proof has the type `Id num (add zero k) k` at an open
index `k`. -/
theorem refl_not_hosted_open_rules (witness : Tower.Tm 1) :
    ¬ Typed rules openIndexCtx (.refl witness)
      (.id numT (addNative zeroNative (.var 0)) (.var 0)) := by
  intro typed
  obtain ⟨A, _, le⟩ := Typed.generation typed
  have target : IsType rules openIndexCtx (.id numT (addNative zeroNative (.var 0)) (.var 0)) :=
    ⟨_, .sort _, .idForm (Derivable.mono (stage_sub_rules _) (numT_typed (Γ := openIndexCtx)
      (List.mem_cons_self (a := numN) (l := [])))) (.sort _) addZeroVar_typed (.var 0)⟩
  have identity := TypeLe.id_eq (S := setting fun _ => 0) facts le target
    openIndexCtx_formed
  obtain ⟨carrierEq, toPoint, toEndpoint⟩ :=
    TypeEq.id_injective facts identity
      openIndexCtx_formed
  obtain ⟨u, hu, carrierEqual⟩ := carrierEq
  exact addZero_ne_var (.convEq (.trans (.symm toPoint) toEndpoint) carrierEqual hu)

end OpenIndex

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
