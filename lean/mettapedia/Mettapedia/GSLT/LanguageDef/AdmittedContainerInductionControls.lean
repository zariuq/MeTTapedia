import Mettapedia.GSLT.LanguageDef.AdmittedContainerInduction
import Mettapedia.GSLT.LanguageDef.AdmittedContainerPredicateControls
import Mettapedia.Logic.HOL.Soundness

/-!
# Original admitted Vector induction with a recursive-tree profile

The original Nil/Cons codes have a length index and ordered length/head
fields. Their retained constructor cases establish non-bottom membership at
arbitrary open inputs. Injectivity and constructor separation remain visible
in the proof context and are validated by the existing recursive-tree model.
This is a source-interpretation control, not a native profile certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerInductionControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open AdmittedContainerHOL AdmittedContainerGeneratedControls
open IndexedContainerPositionTerms FiniteConstructorEncoding
open IndexedInductiveNatVec

noncomputable section

def initial {Γ : Ctx BaseCode} : Subst Symbol [] Γ := fun impossible => nomatch impossible
def num {Γ : Ctx BaseCode} (n : Nat) : Term Symbol Γ number :=
  HOL.weakenCtx Γ (AdmittedContainerGeneratedControls.numeral n)
def ctor {Γ : Ctx BaseCode} : Term Symbol Γ (number ⇒ payload ⇒ (number ⇒ space) ⇒ space) := .const .construct
def bottom {Γ : Ctx BaseCode} : Term Symbol Γ space := .const .bottom
def signature {Γ : Ctx BaseCode} : RecursiveSpacePredicate.Contextual Symbol Γ :=
  recursiveSignature block registered (guards := guards) initial num
    (.const .zero) (.const .successor) bottom ctor
def inv {Γ : Ctx BaseCode} : IndexedConstructorGuards.ConstructorPrograms Symbol Γ :=
  inventory block registered guards initial num

def motive {Γ : Ctx BaseCode} : Term Symbol Γ (space ⇒ number ⇒ .prop) :=
  .lam (.lam (.not (.eq (.var (.vs .vz)) (.const .bottom))))
def injectivity {Γ : Ctx BaseCode} : Formula Symbol Γ := ConstructorInjectivity.statement ctor
def separation {Γ : Ctx BaseCode} : Formula Symbol Γ :=
  .all (σ := number) (.all (σ := payload) (.all (σ := number ⇒ space)
    (.not (.eq
      (.app (.app (.app (.const .construct) (.var (.vs (.vs .vz)))) (.var (.vs .vz))) (.var .vz))
      (.const .bottom)))))
def profile {Γ : Ctx BaseCode} (extra : Formula Symbol Γ) : List (Formula Symbol Γ) :=
  [extra, injectivity, separation]

variable {Γ : Ctx BaseCode} {assumptions : List (Formula Symbol Γ)}

private theorem subst_vars {type : Ty BaseCode} (term : Term Symbol Γ type) :
    HOL.subst (fun index => .var index) term = term :=
  ProofSyntax.term_subst_of_identity (fun _ => rfl) term

private theorem subst_drop_shift {domain type : Ty BaseCode}
    (argument : Term Symbol Γ domain) (term : Term Symbol Γ type) :
    HOL.subst (Subst.comp (Subst.single argument) (fun index => .var (.vs index))) term = term :=
  ProofSyntax.term_subst_of_identity (fun _ => rfl) term

def motive_beta (value : Term Symbol Γ space) (index : Term Symbol Γ number) :
    ProofSyntax Symbol assumptions (.eq (.app (.app motive value) index) (.not (.eq value bottom))) := by
  apply ProofSyntax.castIndices rfl ?_
    (CurriedGuardProgramProofs.beta2 (.not (.eq (.var (.vs .vz)) (.const .bottom))) value index)
  simp only [motive, bottom, instantiate, HOL.subst, Subst.single, Subst.lift]
  rw [show HOL.subst (Subst.single index) (HOL.rename Rename.weaken value) = value from
    PredicateFixedPoint.subst_single_weaken index value]

theorem motive_beta_free (value : Term Symbol Γ space) (index : Term Symbol Γ number) :
    (motive_beta (assumptions := assumptions) value index).FunctionExtensionalityFree := by
  unfold motive_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

def separation_specialize (tag : Term Symbol Γ number) (data : Term Symbol Γ payload)
    (descendants : Term Symbol Γ (number ⇒ space))
    (proof : ProofSyntax Symbol assumptions separation) :
    ProofSyntax Symbol assumptions
      (.not (.eq (.app (.app (.app ctor tag) data) descendants) bottom)) := by
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.allE descendants (ProofSyntax.allE data (ProofSyntax.allE tag proof)))
  simp [instantiate, HOL.subst, Subst.single, Subst.lift, Rename.weaken,
    subst_rename, HOL.subst_comp, subst_drop_shift, subst_vars, ctor, bottom]

theorem separation_specialize_free (tag : Term Symbol Γ number) (data : Term Symbol Γ payload)
    (descendants : Term Symbol Γ (number ⇒ space))
    (proof : ProofSyntax Symbol assumptions separation) (free : proof.FunctionExtensionalityFree) :
    (separation_specialize tag data descendants proof).FunctionExtensionalityFree := by
  unfold separation_specialize
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact free

def sourceCases (extra : Formula Symbol Γ) :
    ScopedSourceIndexedCases block registered guards initial num ctor (.const .zero) (.const .successor) bottom
      (PredicateFixedPoint.intersection signature.least (IndexedPredicateInduction.lift (inv.rootProgram ctor) motive))
      motive (profile extra) := by
  let scope : Subst Symbol Γ signature.constructorContext := Subst.ofRename signature.constructorRenaming
  intro Ξ images occurrence arguments
  let localInventory := inventory block registered guards (Subst.comp scope initial)
    (fun n => HOL.subst scope (num n))
  let shifted := localInventory.subst images
  let data := inventoryArguments reading (codes block registered) occurrence arguments
  let descendants := HOL.subst images signature.constructorChildren
  let tag := shifted.numeral occurrence.val
  let encoded := encode shifted.fields occurrence data
  let value := shifted.constructorValue (HOL.subst images (HOL.subst scope ctor)) occurrence data descendants
  let index := reading.indexTerm (codeAt reading (codes block registered) occurrence)
    (Subst.comp images (Subst.comp scope initial)) arguments
  let predicate : Term Symbol Γ (space ⇒ .prop) :=
    PredicateFixedPoint.intersection signature.least (IndexedPredicateInduction.lift (inv.rootProgram ctor) motive)
  let hypotheses :=
    applyArguments _ (guards.compile (codeAt reading (codes block registered) occurrence)
      (Subst.comp images (Subst.comp scope initial))) arguments ::
    .app (HOL.subst images (signature.constructorScope.childPredicate
      (weaken (weaken (weaken predicate))) signature.constructorChildren))
      (payloadTerm reading (codes block registered) occurrence arguments) ::
    (signature.methodAssumptions (assumptions := profile extra) predicate).map (HOL.subst images)
  change ProofSyntax Symbol hypotheses (.app (.app motive value) index)
  apply ProofSyntax.impE (ProofSyntax.eqPropER (motive_beta value index))
  have available : ProofSyntax Symbol hypotheses (separation (Γ := Ξ)) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp (Const := Symbol) (Δ := hypotheses)
      ⟨6, by simp [hypotheses, RecursiveSpacePredicate.Contextual.methodAssumptions, weakenHyps, profile]⟩)
    change HOL.subst images (weaken (weaken (weaken (separation (Γ := Γ))))) = separation
    rfl
  exact separation_specialize tag encoded descendants available

def member {Γ : Ctx BaseCode} (value : Term Symbol Γ space) (index : Term Symbol Γ number) : Formula Symbol Γ :=
  .app (.app (memberProgram block registered (guards := guards) initial num
    (.const .zero) (.const .successor) bottom ctor) value) index

def nonbottom (value : Term Symbol Γ space) (index : Term Symbol Γ number) :
    ProofSyntax Symbol [injectivity, separation] (.imp (member value index) (.not (.eq value bottom))) := by
  apply ProofSyntax.impI
  have derived := memberInductionFromSourceCases block registered guards initial num ctor
    (.const .zero) (.const .successor) bottom motive
    (ProofSyntax.hyp (Const := Symbol) (Δ := profile (member value index)) ⟨1, by simp [profile]⟩)
    (sourceCases (member value index)) value index
    (ProofSyntax.hyp (Const := Symbol) (Δ := profile (member value index)) ⟨0, by simp [profile]⟩)
  exact .impE (.eqPropEL (motive_beta value index)) derived

theorem sourceCases_free (extra : Formula Symbol Γ)
    {Ξ : Ctx BaseCode} (images : Subst Symbol signature.constructorContext Ξ)
    occurrence arguments :
    (sourceCases extra images occurrence arguments).FunctionExtensionalityFree := by
  unfold sourceCases
  refine ⟨motive_beta_free _ _, ?_⟩
  apply separation_specialize_free
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

theorem nonbottom_free (value : Term Symbol Γ space) (index : Term Symbol Γ number) :
    (nonbottom value index).FunctionExtensionalityFree := by
  unfold nonbottom
  refine ⟨motive_beta_free _ _, ?_⟩
  apply memberInductionFromSourceCases_free
  · trivial
  · exact sourceCases_free _
  · trivial

def statement : ClosedFormula Symbol :=
  .all (σ := space) (.all (σ := number)
    (.imp (member (.var (.vs .vz)) (.var .vz))
      (.not (.eq (.var (.vs .vz)) (.const .bottom)))))

def allProof : ProofSyntax Symbol [injectivity, separation] statement := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.castIndices ?_ rfl (nonbottom (.var (.vs .vz)) (.var .vz))
  rfl

theorem allProof_free : allProof.FunctionExtensionalityFree := by
  unfold allProof
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact nonbottom_free _ _

theorem injectivity_valid : model.models (injectivity (Γ := [])) := by
  intro firstTag _ firstData _ firstChildren _ secondTag _ secondData _ secondChildren _
  change (ULift.up (Mettapedia.TypeTheory.RecursiveSpace.construct firstTag.down firstData
      (fun n => (firstChildren (.up n)).down)) =
    ULift.up (Mettapedia.TypeTheory.RecursiveSpace.construct secondTag.down secondData
      (fun n => (secondChildren (.up n)).down))) ↔
    model.Eqv number firstTag secondTag ∧
      (model.Eqv payload firstData secondData ∧ model.Eqv (number ⇒ space) firstChildren secondChildren)
  simp only [model.eqv_iff_eq_of_fullDomains full]
  constructor
  · intro same
    obtain ⟨tags, data, descendants⟩ :=
      (Mettapedia.TypeTheory.RecursiveSpace.construct_injective _ _ _ _ _ _).mp (congrArg ULift.down same)
    refine ⟨congrArg ULift.up tags, data, ?_⟩
    funext n
    apply ULift.ext
    exact congrFun descendants n.down
  · rintro ⟨tags, data, descendants⟩
    cases tags
    cases data
    cases descendants
    rfl

theorem separation_valid : model.models (separation (Γ := [])) := by
  intro tag _ data _ descendants _ impossible
  exact Mettapedia.TypeTheory.RecursiveSpace.construct_ne_bottom tag.down data
    (fun n => (descendants (.up n)).down) (congrArg ULift.down impossible)

theorem statement_valid : model.models statement := by
  have checked := Soundness.extTheorem_sound (ProofSyntax.impI (ProofSyntax.impI allProof)).erase model
    (model.functionsRespectEqv_of_fullDomains full)
  exact (HenkinModel.models_imp model).mp
    ((HenkinModel.models_imp model).mp checked separation_valid) injectivity_valid

private theorem empty_values_unique (values : model.Valuation []) : @values = @empty := by
  funext type index
  exact nomatch index

private theorem models_at_empty (formula : ClosedFormula Symbol) :
    model.models formula ↔ (model.denote formula empty).down := by
  unfold HenkinModel.models PreModel.models
  apply Iff.of_eq
  exact congrArg (fun values : model.Valuation [] => (model.denote formula values).down)
    (empty_values_unique _)

theorem num_meaning (values : model.Valuation Γ) (n : Nat) :
    model.denote (num n) values = interpreted.numbers n := by
  have closed (valuation : model.Valuation []) :
      model.denote (AdmittedContainerGeneratedControls.numeral n) valuation = interpreted.numbers n := by
    rw [empty_values_unique valuation]
    exact AdmittedContainerGeneratedControls.numeral_meaning n
  rw [num, model.denote_weakenCtx]
  exact closed _

theorem open_program_exact (values : model.Valuation Γ) (value : Ty.denote model.Carrier space)
    (index : Natural.Carrier) :
    (model.denote (memberProgram block registered (guards := guards) initial num
      (.const .zero) (.const .successor) bottom ctor) values value (interpreted.index index)).down ↔
      Mettapedia.TypeTheory.IndexedPolynomial.Algebra.Generated algebra environment index value := by
  have represented : interpreted.Represents environment (initial (Γ := Γ)) values := by
    intro _ impossible
    exact nomatch impossible
  exact memberProgram_denote block registered sourceOrder interpreted images initial num values environment represented
    (.const .zero) (.const .successor) full empty
    AdmittedContainerPredicateControls.Closed.zero_meaning AdmittedContainerPredicateControls.Closed.successor_meaning
    bottom ctor injections constructor_shape_separation index_injective (num_meaning values) value index

theorem vector_nonbottom (value : Ty.denote model.Carrier space) (index : Natural.Carrier)
    (present : (model.denote AdmittedContainerPredicateControls.Closed.program empty value (interpreted.index index)).down) :
    value ≠ model.denote bottomCode empty := by
  let values : model.Valuation [number, space] := model.extend (model.extend empty value) (interpreted.index index)
  have generated := (AdmittedContainerPredicateControls.Closed.program_exact value index).mp present
  have localMember := (open_program_exact values value index).mpr generated
  have every := (models_at_empty statement).mp statement_valid
  exact every value (full _ _) (interpreted.index index) (full _ _) localMember

theorem nil_nonbottom : nilValue ≠ model.denote bottomCode empty :=
  vector_nonbottom nilValue Natural.zero
    AdmittedContainerPredicateControls.Closed.nil_member

theorem cons_nonbottom (head : Bool) : consValue head ≠ model.denote bottomCode empty :=
  vector_nonbottom (consValue head)
    (Natural.succ Natural.zero)
    (AdmittedContainerPredicateControls.Closed.cons_member head)

def consRoot : ProofSyntax Symbol []
    (.app (.app (constructorInventory.rootProgram constructorCode) consProgram) consIndex) :=
  .impE (.eqPropER (constructorInventory.rootProgram_beta constructorCode consProgram consIndex))
    (rootProof block registered guards Subst.id AdmittedContainerGeneratedControls.numeral constructorCode
      bottomChildren consOccurrence consArguments consEvidence)

def nilRoot : ProofSyntax Symbol []
    (.app (.app (constructorInventory.rootProgram constructorCode) nilProgram) nilIndex) :=
  .impE (.eqPropER (constructorInventory.rootProgram_beta constructorCode nilProgram nilIndex))
    (rootProof block registered guards Subst.id AdmittedContainerGeneratedControls.numeral constructorCode
      bottomChildren nilOccurrence nilArguments nilEvidence)

theorem consRoot_free : consRoot.FunctionExtensionalityFree := by
  unfold consRoot
  exact ⟨constructorInventory.rootProgram_beta_free _ _ _,
    rootProof_free _ _ _ _ _ _ _ _ _ _ consEvidence_free⟩

def wrongRoot : ClosedFormula Symbol :=
  .app (.app (constructorInventory.rootProgram constructorCode) nilProgram) consIndex

def wrongRootIndex : ProofSyntax Symbol [injectivity] (.imp wrongRoot (.eq nilIndex consIndex)) := by
  apply ProofSyntax.impI
  have root : ProofSyntax Symbol [wrongRoot, injectivity]
      (constructorInventory.rootIndex constructorCode nilProgram consIndex) :=
    .impE (.eqPropEL (constructorInventory.rootProgram_beta constructorCode nilProgram consIndex)) (.hyp 0)
  have compared := constructorInventory.rootIndex_result constructorCode nilOccurrence
    (inventoryArguments reading (codes block registered) nilOccurrence nilArguments) bottomChildren consIndex
    (ProofSyntax.hyp (Const := Symbol) (Δ := [wrongRoot, injectivity]) 1) root
  have original := guards.inventoryResultProof (assumptions := [wrongRoot, injectivity])
    (codes block registered) Subst.id AdmittedContainerGeneratedControls.numeral nilOccurrence nilArguments
  exact .eqTrans (.eqSymm original) compared

theorem wrongRootIndex_free : wrongRootIndex.FunctionExtensionalityFree := by
  unfold wrongRootIndex
  refine ⟨?_, ?_⟩
  · exact guards.inventoryResultProof_free _ _ _ _ _
  · apply IndexedConstructorGuards.ConstructorPrograms.rootIndex_result_free
    · trivial
    · exact ⟨constructorInventory.rootProgram_beta_free _ _ _, True.intro⟩

theorem wrongRoot_refused : ¬ model.models wrongRoot := by
  intro present
  have sound := Soundness.extTheorem_sound (ProofSyntax.impI wrongRootIndex).erase model
    (model.functionsRespectEqv_of_fullDomains full)
  have impossible := (HenkinModel.models_imp model).mp
    ((HenkinModel.models_imp model).mp sound injectivity_valid) present
  have interpretedEqual := (models_at_empty (.eq nilIndex consIndex)).mp impossible
  have valuesEqual : model.denote nilIndex empty = model.denote consIndex empty :=
    (model.eqv_iff_eq_of_fullDomains full _ _).mp interpretedEqual
  have sourceEqual : interpreted.index Natural.zero = interpreted.index (Natural.succ Natural.zero) :=
    nilIndex_meaning.symm.trans (valuesEqual.trans consIndex_meaning)
  exact Natural.succ_ne_zero Natural.zero (index_injective sourceEqual).symm

def collapsedModel : HenkinModel.{0,0,0} BaseCode Symbol := .standard carrier (fun symbol => match symbol with
  | .zero => .up 0
  | .successor => fun n => .up (n.down + 1)
  | .addition => fun n m => .up (n.down + m.down)
  | .flagTrue => .up true
  | .bottom => .up Mettapedia.TypeTheory.RecursiveSpace.bottom
  | .construct => fun _ _ _ => model.denote nilProgram empty)

theorem collapsed_full : collapsedModel.FullDomains := HenkinModel.fullDomains_standard _ _

theorem collapsed_separation_valid : collapsedModel.models (separation (Γ := [])) := by
  intro tag _ data _ descendants _ impossible
  exact constructor_separated _ _ _ impossible

theorem collapsed_wrongRoot_valid : collapsedModel.models wrongRoot := by
  have accepted := Soundness.extTheorem_sound consRoot.erase collapsedModel
    (collapsedModel.functionsRespectEqv_of_fullDomains collapsed_full)
  exact accepted

theorem collapsed_nilRoot_valid : collapsedModel.models
    (.app (.app (constructorInventory.rootProgram constructorCode) nilProgram) nilIndex) :=
  Soundness.extTheorem_sound nilRoot.erase collapsedModel
    (collapsedModel.functionsRespectEqv_of_fullDomains collapsed_full)

theorem collapsed_injectivity_invalid : ¬ collapsedModel.models (injectivity (Γ := [])) := by
  intro assumed
  let data := model.denote (payloadTerm reading (codes block registered) nilOccurrence nilArguments) empty
  let descendants : Ty.denote collapsedModel.Carrier (number ⇒ space) := fun _ => model.denote bottomCode empty
  have compared := assumed (ULift.up 0) True.intro data True.intro descendants True.intro
    (ULift.up 1) True.intro data True.intro descendants True.intro
  have fields := compared.mp rfl
  have impossible := (collapsedModel.eqv_iff_eq_of_fullDomains collapsed_full _ _).mp fields.1
  exact Nat.zero_ne_one (congrArg ULift.down impossible)

theorem injectivity_cannot_be_dropped :
    ¬ Nonempty (ProofSyntax Symbol [] (.not wrongRoot)) := by
  rintro ⟨proof⟩
  have impossible := Soundness.extTheorem_sound proof.erase collapsedModel
    (collapsedModel.functionsRespectEqv_of_fullDomains collapsed_full)
  exact (HenkinModel.models_not collapsedModel).mp impossible collapsed_wrongRoot_valid

#print axioms motive_beta
#print axioms separation_specialize
#print axioms separation_specialize_free
#print axioms sourceCases
#print axioms nonbottom
#print axioms sourceCases_free
#print axioms nonbottom_free
#print axioms allProof
#print axioms allProof_free
#print axioms injectivity_valid
#print axioms separation_valid
#print axioms statement_valid
#print axioms open_program_exact
#print axioms vector_nonbottom
#print axioms nil_nonbottom
#print axioms cons_nonbottom
#print axioms consRoot
#print axioms nilRoot
#print axioms consRoot_free
#print axioms wrongRootIndex
#print axioms wrongRootIndex_free
#print axioms wrongRoot_refused
#print axioms collapsed_wrongRoot_valid
#print axioms collapsed_nilRoot_valid
#print axioms collapsed_separation_valid
#print axioms collapsed_injectivity_invalid
#print axioms injectivity_cannot_be_dropped
end
end Mettapedia.GSLT.LanguageDef.AdmittedContainerInductionControls
