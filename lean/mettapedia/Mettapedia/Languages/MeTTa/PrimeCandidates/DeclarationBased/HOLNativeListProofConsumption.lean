import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListProofInputs

/-!
# Applying the retained native fusion proof to predicate witnesses

The already compiled and interpreted proof is specialized at arbitrary
well-typed native functions and lists in a formed mixed context. Predicate
consumption uses its actual Leibniz proof, not a second proof of fusion.
The predicate ranges over the existing HOL proposition carrier; no identity
with native Id or quantification over arbitrary universe families is asserted.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeListProofConsumption

open Presentation Presentation.FormationSensitive Presentation.ConstantExpansion
open NativeIndexedFamilies IntrinsicMaps
open HOLNativeListConstantBodies (rules Typing bodies)
open FormationSensitiveHOLProofFamily (proof universalProposition)
open FormationSensitiveHOLUniformList (rawAll rawMap)
open FormationSensitiveMixedLeibnizRules (eqFormula)
open Mettapedia.Logic HOL.UniformListInduction
open Presentation.SchemaElaboration
open FormationSensitiveMixedHOLProofRules

variable {n m : Nat}

def listType (element : Tower.Tm 0) : Tower.Tm n := liftClosed (Intrinsic.listApp element)
def functionType (element : Tower.Tm 0) : Tower.Tm n := liftClosed (arrow element element)
def mapTerm (element : Tower.Tm 0) : Tower.Tm n :=
  liftClosed (HOLNativeListConstantBodies.mapBody element)
def mapped (element : Tower.Tm 0) (function list : Tower.Tm n) : Tower.Tm n :=
  .app (.app (mapTerm element) function) list
def unfused (element : Tower.Tm 0) (f g xs : Tower.Tm n) : Tower.Tm n :=
  mapped element f (mapped element g xs)
def fused (element : Tower.Tm 0) (f g xs : Tower.Tm n) : Tower.Tm n :=
  mapped element (IntrinsicNativeListMapComputation.compose f g) xs
def fusionFormula (element : Tower.Tm 0) (f g xs : Tower.Tm n) : Tower.Tm n :=
  eqFormula (listType element) (unfused element f g xs) (fused element f g xs)
def listsFormula (element : Tower.Tm 0) (f g : Tower.Tm n) : Tower.Tm n :=
  universalProposition (listType element)
    (.lam (fusionFormula element (rename wk f) (rename wk g) (.var 0)))
def functionsFormula (element : Tower.Tm 0) (f : Tower.Tm n) : Tower.Tm n :=
  universalProposition (functionType element)
    (.lam (listsFormula element (rename wk f) (.var 0)))
def fusionClaim (element : Tower.Tm 0) : Tower.Tm n :=
  universalProposition (functionType element) (.lam (functionsFormula element (.var 0)))

theorem functionType_eq (element : Tower.Tm 0) :
    (functionType element : Tower.Tm n) = arrow (liftClosed element) (liftClosed element) := by
  simp only [functionType, liftClosed, rename_arrow]

theorem listType_native (element : Tower.Tm 0) :
    (listType element : Tower.Tm n) = Intrinsic.listApp (liftClosed element) := rfl

theorem mapped_native (element : Tower.Tm 0) (f xs : Tower.Tm n) :
    mapped element f xs = IntrinsicNativeListMapComputation.applyMap
      (liftClosed element) (liftClosed element) f xs := rfl

theorem subst_lifted (sigma : Sub Tower.Head n m) (term : Tower.Tm 0) :
    subst sigma (liftClosed term) = liftClosed term := by
  simp only [liftClosed, subst_rename]
  have same : (fun index : Fin 0 => sigma (Fin.elim0 index)) =
      renSub (Fin.elim0 : Ren 0 m) := by funext index; exact Fin.elim0 index
  rw [same, subst_renSub]

theorem rename_lifted (rho : Ren n m) (term : Tower.Tm 0) :
    rename rho (liftClosed term) = liftClosed term := by
  simp only [liftClosed, rename_comp]
  apply rename_ext
  intro index
  exact Fin.elim0 index

theorem eqFormula_subst (sigma : Sub Tower.Head n m) (domain left right : Tower.Tm n) :
    subst sigma (eqFormula domain left right) =
      eqFormula (subst sigma domain) (subst sigma left) (subst sigma right) := by
  simp [eqFormula, FormationSensitiveMixedLeibnizRules.predicateType,
    FormationSensitiveMixedLeibnizRules.atPredicate,
    universalProposition, FormationSensitiveHOLUniformList.rawImp, subst,
    subst_rename, rename_subst, liftSub, wk]

theorem fusionFormula_subst (sigma : Sub Tower.Head n m)
    (element : Tower.Tm 0) (f g xs : Tower.Tm n) :
    subst sigma (fusionFormula element f g xs) =
      fusionFormula element (subst sigma f) (subst sigma g) (subst sigma xs) := by
  simp [fusionFormula, eqFormula_subst, unfused, fused, mapped, mapTerm, listType,
    IntrinsicNativeListMapComputation.compose, subst,
    subst_rename, rename_subst, liftSub, wk]

theorem listsFormula_subst (sigma : Sub Tower.Head n m)
    (element : Tower.Tm 0) (f g : Tower.Tm n) :
    subst sigma (listsFormula element f g) =
      listsFormula element (subst sigma f) (subst sigma g) := by
  simp [listsFormula, universalProposition, subst, listType,
    fusionFormula_subst, subst_rename, rename_subst, liftSub, wk]

theorem functionsFormula_subst (sigma : Sub Tower.Head n m)
    (element : Tower.Tm 0) (f : Tower.Tm n) :
    subst sigma (functionsFormula element f) = functionsFormula element (subst sigma f) := by
  simp [functionsFormula, universalProposition, subst, functionType,
    listsFormula_subst, subst_rename, rename_subst, liftSub, wk]

theorem listType_typed {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) (context : Tower.Ctx n) :
    Typing context (listType element) (sortTm Tower.zero) :=
  FormationSensitiveHOLInterface.closed_typed
    (HOLNativeListConstantBodies.list_typed elementTyped) context

theorem functionType_typed {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) (context : Tower.Ctx n) :
    Typing context (functionType element) (sortTm Tower.zero) :=
  FormationSensitiveHOLInterface.closed_typed
    (pi_zero elementTyped elementTyped.weaken) context

theorem mapped_typed {element : Tower.Tm 0} {context : Tower.Ctx n}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) {f xs : Tower.Tm n}
    (fTyped : Typing context f (functionType element))
    (xsTyped : Typing context xs (listType element)) :
    Typing context (mapped element f xs) (listType element) := by
  have symbol := FormationSensitiveHOLInterface.closed_typed
    (HOLNativeListConstantBodies.map_typed elementTyped) context
  simp only [rename_arrow, liftClosed] at symbol
  rw [functionType_eq] at fTyped
  have first := Typing.appElim symbol fTyped
  simp only [arrow, inst0_rename_wk] at first
  simpa only [mapped, mapTerm, listType, liftClosed, arrow, inst0_rename_wk] using
    Typing.appElim first xsTyped

theorem compose_typed {element : Tower.Tm 0} {context : Tower.Ctx n}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) {f g : Tower.Tm n}
    (fTyped : Typing context f (functionType element))
    (gTyped : Typing context g (functionType element)) :
    Typing context (IntrinsicNativeListMapComputation.compose f g) (functionType element) := by
  have formed := functionType_typed elementTyped context
  rw [functionType_eq] at formed ⊢ fTyped gTyped
  apply Typing.lamIntro formed (.sort Tower.zero)
  have fLift := fTyped.weaken (extension := liftClosed element)
  have gLift := gTyped.weaken (extension := liftClosed element)
  simp only [rename_arrow] at fLift gLift
  have first := Typing.appElim gLift (Typing.var 0)
  simp only [inst0_rename_wk] at first
  simpa only [arrow, inst0_rename_wk] using Typing.appElim fLift first

theorem fusionFormula_typed {element : Tower.Tm 0} {context : Tower.Ctx n}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) {f g xs : Tower.Tm n}
    (fTyped : Typing context f (functionType element))
    (gTyped : Typing context g (functionType element))
    (xsTyped : Typing context xs (listType element)) :
    Typing context (fusionFormula element f g xs) (.const `HOLUniformList.prop) :=
  FormationSensitiveMixedLeibnizRules.eqFormula_typed (listType_typed elementTyped context)
    (mapped_typed elementTyped fTyped (mapped_typed elementTyped gTyped xsTyped))
    (mapped_typed elementTyped (compose_typed elementTyped fTyped gTyped) xsTyped)

theorem listsFormula_typed {element : Tower.Tm 0} {context : Tower.Ctx n}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) {f g : Tower.Tm n}
    (fTyped : Typing context f (functionType element))
    (gTyped : Typing context g (functionType element)) :
    Typing context (listsFormula element f g) (.const `HOLUniformList.prop) := by
  apply universal_lambda_proposition (listType_typed elementTyped context)
  have fLift := fTyped.weaken (extension := listType element)
  have gLift := gTyped.weaken (extension := listType element)
  simp only [functionType, rename_lifted] at fLift gLift
  apply fusionFormula_typed elementTyped fLift gLift
  simpa only [Ctx.lookup_snoc_zero, listType, rename_lifted] using
    (Typing.var (R := rules) (Γ := .snoc context (listType element)) 0)

theorem functionsFormula_typed {element : Tower.Tm 0} {context : Tower.Ctx n}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) {f : Tower.Tm n}
    (fTyped : Typing context f (functionType element)) :
    Typing context (functionsFormula element f) (.const `HOLUniformList.prop) := by
  apply universal_lambda_proposition (functionType_typed elementTyped context)
  have fLift := fTyped.weaken (extension := functionType element)
  simp only [functionType, rename_lifted] at fLift
  apply listsFormula_typed elementTyped fLift
  simpa only [Ctx.lookup_snoc_zero, functionType, rename_lifted] using
    (Typing.var (R := rules) (Γ := .snoc context (functionType element)) 0)

theorem fusionClaim_typed {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) (context : Tower.Ctx n) :
    Typing context (fusionClaim element) (.const `HOLUniformList.prop) := by
  apply universal_lambda_proposition (functionType_typed elementTyped context)
  apply functionsFormula_typed elementTyped
  simpa only [Ctx.lookup_snoc_zero, functionType, rename_lifted] using
    (Typing.var (R := rules) (Γ := .snoc context (functionType element)) 0)

def sourceBody (f g xs : Tower.Tm n) : Tower.Tm n :=
  .app (.app (liftClosed (FormationSensitiveHOLLeibnizInterface.equality sequence))
    (rawMap f (rawMap g xs)))
    (rawMap (IntrinsicNativeListMapComputation.compose f g) xs)

def sourceFusion : Tower.Tm n :=
  rawAll mapping (rawAll mapping (rawAll sequence
    (sourceBody (.var 2) (.var 1) (.var 0))))

def sourceLeibnizFusion : Tower.Tm n :=
  rawAll mapping (rawAll mapping (rawAll sequence
    (FormationSensitiveHOLLeibnizInterface.rawLeibniz sequence
      (rawMap (.var 2) (rawMap (.var 1) (.var 0)))
      (rawMap (IntrinsicNativeListMapComputation.compose (.var 2) (.var 1)) (.var 0)))))

theorem source_represented :
    HOLLeibnizNativeProofTranslation.represent (HOL.UniformListMapFusion.mapFusion (Γ := [])) =
      some (sourceFusion : Tower.Tm 0) := rfl

theorem source_equality_conversion :
    Conv FormationSensitiveHOLProofFamily.rules.headEq (sourceFusion : Tower.Tm n)
      sourceLeibnizFusion FormationSensitiveHOLProofFamily.rules.computation := by
  apply Conv.congApp (.refl _) (Conv.congLam ?_)
  apply Conv.congApp (.refl _) (Conv.congLam ?_)
  apply Conv.congApp (.refl _) (Conv.congLam ?_)
  exact FormationSensitiveHOLLeibnizInterface.Decoded.include_conversion
    (FormationSensitiveHOLLeibnizInterface.equality_application_conversion sequence _ _)

theorem expand_predicate_equality (element : Tower.Tm 0)
    (type : HOL.Ty BaseSort) (left right : Tower.Tm n) :
    expand (bodies element) (FormationSensitiveHOLLeibnizInterface.rawLeibniz type left right) =
      eqFormula (FormationSensitiveHOLInterface.typeAt (HOLNativeListConstantBodies.types element) n type)
        (expand (bodies element) left) (expand (bodies element) right) := by
  simp only [FormationSensitiveHOLLeibnizInterface.rawLeibniz,
    HOLNativeListInduction.expand_rawAll, FormationSensitiveHOLInterface.typeAt,
    eqFormula, FormationSensitiveMixedLeibnizRules.predicateType,
    FormationSensitiveMixedLeibnizRules.atPredicate,
    FormationSensitiveHOLUniformList.rawImp, expand, expand_rename,
    HOLNativeListConstantBodies.bodies_implication, liftClosed, rename]
  rfl

theorem expand_map (element : Tower.Tm 0) (function list : Tower.Tm n) :
    expand (bodies element) (rawMap function list) =
      mapped element (expand (bodies element) function) (expand (bodies element) list) := by
  simp only [rawMap, expand, HOLNativeListConstantBodies.bodies_map, mapped, mapTerm]

theorem expand_compose (element : Tower.Tm 0) (f g : Tower.Tm n) :
    expand (bodies element) (IntrinsicNativeListMapComputation.compose f g) =
      IntrinsicNativeListMapComputation.compose (expand (bodies element) f)
        (expand (bodies element) g) := by
  simp only [IntrinsicNativeListMapComputation.compose, expand, expand_rename]

theorem mapped_functionType (element : Tower.Tm 0) :
    FormationSensitiveHOLInterface.typeAt (HOLNativeListConstantBodies.types element) n mapping =
      functionType element := by
  simp only [FormationSensitiveHOLInterface.typeAt, HOLNativeListConstantBodies.types,
    functionType, liftClosed, rename_arrow]
  change (liftClosed element).pi (liftClosed element) =
    arrow (liftClosed element) (liftClosed element)
  rw [arrow, rename_lifted]

theorem source_expanded (element : Tower.Tm 0) :
    expand (bodies element) (sourceLeibnizFusion : Tower.Tm n) = fusionClaim element := by
  simp only [sourceLeibnizFusion, HOLNativeListInduction.expand_rawAll,
    expand_predicate_equality, expand_map, expand_compose, mapped_functionType,
    fusionClaim, functionsFormula, listsFormula, fusionFormula, unfused, fused,
    expand, rename, wk]
  rfl

theorem native_claim {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) :
    Typing .nil (HOLNativeListProofInputs.nativeMapFusionProof element)
      (proof (fusionClaim element)) := by
  obtain ⟨code, represented, checked⟩ := HOLNativeListProofInputs.native_map_fusion elementTyped
  have same : code = sourceFusion := Option.some.inj (represented.symm.trans source_represented)
  subst code
  have converted := (HOLNativeListDeclarationInterpretation.interpretation elementTyped).conversion
    (source_equality_conversion (n := 0))
  rw [source_expanded] at converted
  exact .conv checked.typing (proof_formed (fusionClaim_typed elementTyped .nil))
    (.sort Tower.zero) (Conv.congApp (.refl _) converted)

theorem functionsFormula_rename (rho : Ren n m) (element : Tower.Tm 0) (f : Tower.Tm n) :
    rename rho (functionsFormula element f) = functionsFormula element (rename rho f) := by
  simpa only [subst_renSub] using functionsFormula_subst (renSub rho) element f

theorem fusionClaim_rename (rho : Ren n m) (element : Tower.Tm 0) :
    rename rho (fusionClaim element) = fusionClaim element := by
  simp only [fusionClaim, universalProposition, rename, functionType, rename_lifted,
    functionsFormula_rename, liftRen, Fin.cases_zero]

theorem instantiate_functions (element : Tower.Tm 0) (f : Tower.Tm n) :
    inst0 f (functionsFormula element (.var 0)) = functionsFormula element f := by
  simp only [inst0, functionsFormula_subst, subst, subst0, Fin.cases_zero]

theorem instantiate_lists (element : Tower.Tm 0) (f g : Tower.Tm n) :
    inst0 g (listsFormula element (rename wk f) (.var 0)) = listsFormula element f g := by
  change subst (subst0 g) (listsFormula element (rename wk f) (.var 0)) = _
  rw [listsFormula_subst]
  change listsFormula element (inst0 g (rename wk f)) g = _
  rw [inst0_rename_wk]

theorem instantiate_fusion (element : Tower.Tm 0) (f g xs : Tower.Tm n) :
    inst0 xs (fusionFormula element (rename wk f) (rename wk g) (.var 0)) =
      fusionFormula element f g xs := by
  change subst (subst0 xs) (fusionFormula element (rename wk f) (rename wk g) (.var 0)) = _
  rw [fusionFormula_subst]
  change fusionFormula element (inst0 xs (rename wk f)) (inst0 xs (rename wk g)) xs = _
  rw [inst0_rename_wk, inst0_rename_wk]

def appliedProof (element : Tower.Tm 0) (f g xs : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (liftClosed (HOLNativeListProofInputs.nativeMapFusionProof element)) f) g) xs

/-- Specialization accepts arbitrary mixed-native operands. Only the element
interpretation is closed; no source-syntax representation of f, g or xs is
required, and the proof head is the previously checked compiler output. -/
theorem appliedProof_typed {element : Tower.Tm 0} {context : Tower.Ctx n}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) {f g xs : Tower.Tm n}
    (fTyped : Typing context f (functionType element))
    (gTyped : Typing context g (functionType element))
    (xsTyped : Typing context xs (listType element)) :
    Typing context (appliedProof element f g xs) (proof (fusionFormula element f g xs)) := by
  have lifted := FormationSensitiveHOLInterface.closed_typed (native_claim elementTyped) context
  have major : Typing context (liftClosed (HOLNativeListProofInputs.nativeMapFusionProof element))
      (proof (fusionClaim element)) := by
    simpa only [liftClosed, FormationSensitiveHOLProofFamily.proof_rename,
      fusionClaim_rename] using lifted
  have variableFunction : Typing (.snoc context (functionType element)) (.var 0)
      (functionType element) := by
    simpa only [Ctx.lookup_snoc_zero, functionType, rename_lifted] using
      (Typing.var (R := rules) (Γ := .snoc context (functionType element)) 0)
  have first := universal_elim (functionType_typed elementTyped context)
    (functionsFormula_typed elementTyped variableFunction) major fTyped
  rw [instantiate_functions] at first
  have fFunctionLift := fTyped.weaken (extension := functionType element)
  simp only [functionType, rename_lifted] at fFunctionLift
  have second := universal_elim (functionType_typed elementTyped context)
    (listsFormula_typed elementTyped fFunctionLift variableFunction) first gTyped
  rw [instantiate_lists] at second
  have fListLift := fTyped.weaken (extension := listType element)
  have gListLift := gTyped.weaken (extension := listType element)
  simp only [functionType, rename_lifted] at fListLift gListLift
  have variableList : Typing (.snoc context (listType element)) (.var 0)
      (listType element) := by
    simpa only [Ctx.lookup_snoc_zero, listType, rename_lifted] using
      (Typing.var (R := rules) (Γ := .snoc context (listType element)) 0)
  have third := universal_elim (listType_typed elementTyped context)
    (fusionFormula_typed elementTyped fListLift gListLift variableList) second xsTyped
  simpa only [appliedProof, instantiate_fusion] using third

def consume (element : Tower.Tm 0) (f g xs predicate input : Tower.Tm n) : Tower.Tm n :=
  .app (.app (appliedProof element f g xs) predicate) input

/-- This is actual use of the retained compiled proof at an arbitrary HOL
predicate on native lists, followed by the supplied predicate witness. -/
theorem consume_typed {element : Tower.Tm 0} {context : Tower.Ctx n}
    (elementTyped : Typing .nil element (sortTm Tower.zero))
    {f g xs predicate input : Tower.Tm n}
    (fTyped : Typing context f (functionType element))
    (gTyped : Typing context g (functionType element))
    (xsTyped : Typing context xs (listType element))
    (predicateTyped : Typing context predicate
      (FormationSensitiveMixedLeibnizRules.predicateType (listType element)))
    (inputTyped : Typing context input (proof (.app predicate (unfused element f g xs)))) :
    Typing context (consume element f g xs predicate input)
      (proof (.app predicate (fused element f g xs))) :=
  FormationSensitiveMixedLeibnizRules.elimination
    (listType_typed elementTyped context)
    (mapped_typed elementTyped fTyped (mapped_typed elementTyped gTyped xsTyped))
    (mapped_typed elementTyped (compose_typed elementTyped fTyped gTyped) xsTyped)
    (appliedProof_typed elementTyped fTyped gTyped xsTyped) predicateTyped inputTyped

theorem consume_judgment {element : Tower.Tm 0} {context : Tower.Ctx n}
    (contextFormed : ContextFormation rules context)
    (elementTyped : Typing .nil element (sortTm Tower.zero))
    {f g xs predicate input : Tower.Tm n}
    (fTyped : Typing context f (functionType element))
    (gTyped : Typing context g (functionType element))
    (xsTyped : Typing context xs (listType element))
    (predicateTyped : Typing context predicate
      (FormationSensitiveMixedLeibnizRules.predicateType (listType element)))
    (inputTyped : Typing context input (proof (.app predicate (unfused element f g xs)))) :
    Judgment rules context (consume element f g xs predicate input)
      (proof (.app predicate (fused element f g xs))) :=
  ⟨contextFormed, consume_typed elementTyped fTyped gTyped xsTyped predicateTyped inputTyped⟩

/-- The public application law displayed using the existing native List/map
operations, with no intervening source-expression restriction on the caller. -/
theorem consume_native_judgment {element : Tower.Tm 0} {context : Tower.Ctx n}
    (contextFormed : ContextFormation rules context)
    (elementTyped : Typing .nil element (sortTm Tower.zero))
    {f g xs predicate input : Tower.Tm n}
    (fTyped : Typing context f (arrow (liftClosed element) (liftClosed element)))
    (gTyped : Typing context g (arrow (liftClosed element) (liftClosed element)))
    (xsTyped : Typing context xs (Intrinsic.listApp (liftClosed element)))
    (predicateTyped : Typing context predicate
      (.pi (Intrinsic.listApp (liftClosed element)) (.const `HOLUniformList.prop)))
    (inputTyped : Typing context input (proof (.app predicate
      (IntrinsicNativeListMapComputation.applyMap (liftClosed element) (liftClosed element) f
        (IntrinsicNativeListMapComputation.applyMap (liftClosed element) (liftClosed element) g xs))))) :
    Judgment rules context (consume element f g xs predicate input)
      (proof (.app predicate
        (IntrinsicNativeListMapComputation.applyMap (liftClosed element) (liftClosed element)
          (IntrinsicNativeListMapComputation.compose f g) xs))) := by
  have first : Typing context f (functionType element) := by
    simpa only [functionType_eq] using fTyped
  have second : Typing context g (functionType element) := by
    simpa only [functionType_eq] using gTyped
  simpa only [fused, mapped_native] using
    consume_judgment contextFormed elementTyped first second xsTyped predicateTyped inputTyped

/-- The target predicate family is not erased by a decoder rule merely
because a fusion proof transports its witness. This is a root-shape control,
not a claim about the whole conversion class of an arbitrary predicate. -/
theorem predicate_result_not_decoder (element : Tower.Tm 0) (predicate : Fin n)
    (f g xs target : Tower.Tm n) :
    ¬ FormationSensitiveHOLProofFamily.DecoderStep
      (proof (.app (.var predicate) (fused element f g xs))) target := by
  intro decoded
  cases decoded

#print axioms source_equality_conversion
#print axioms source_expanded
#print axioms native_claim
#print axioms appliedProof_typed
#print axioms consume_typed
#print axioms consume_judgment
#print axioms consume_native_judgment
#print axioms predicate_result_not_decoder

end HOLNativeListProofConsumption
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
