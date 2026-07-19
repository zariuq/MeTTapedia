import Mettapedia.Languages.MeTTa.HE.HumanTypePresentationExact

/-!
# Alpha-exact observations for runtime type packages

Exact runtime type packages are unique only up to the private variable names
introduced at inference sites.  This module states the smallest observation
relation needed by ordered evaluator consumers: literal candidates agree
exactly, while insulated inferred candidates may be two injective renamings
of one common type shape.  Order and multiplicity remain visible.

The relation is structural and executable-independent.  In particular, it
does not choose a canonical private spelling.  Candidate scans may use it
under negation only after proving their match and arrow-skeleton invariance.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanTypePresentationAlpha

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanTypeSpec
open HumanTypePresentation
open HumanTypeRuntimeRefinement
open HumanTypePresentationExact

/-- Two observed types are alpha siblings when both are injective renamings
of one common type shape. -/
def ObservedTypeAlphaRel (left right : Atom) : Prop :=
  ∃ source,
    TypeVariableRenamingOf source left ∧
      TypeVariableRenamingOf source right

@[refl] theorem ObservedTypeAlphaRel.refl (type : Atom) :
    ObservedTypeAlphaRel type type :=
  ⟨type, TypeVariableRenamingOf.refl type,
    TypeVariableRenamingOf.refl type⟩

theorem ObservedTypeAlphaRel.symm {left right : Atom}
    (alpha : ObservedTypeAlphaRel left right) :
    ObservedTypeAlphaRel right left := by
  rcases alpha with ⟨source, hleft, hright⟩
  exact ⟨source, hright, hleft⟩

/-- Variables introduced by one private presentation avoid every public name
visible to its consumer. -/
def TypeVariablesInsulated (publicNames : List String) (type : Atom) : Prop :=
  ∀ name ∈ TypeSubst.typeVars type, name ∉ publicNames

private theorem typeVars_mem_typeVarsList_of_mem
    {type : Atom} {types : List Atom} (htype : type ∈ types) :
    ∀ name, name ∈ TypeSubst.typeVars type →
      name ∈ TypeSubst.typeVarsList types := by
  induction types with
  | nil => simp at htype
  | cons head tail ih =>
      simp only [List.mem_cons] at htype
      rcases htype with rfl | htail
      · intro name hname
        simp [TypeSubst.typeVarsList, hname]
      · intro name hname
        simp only [TypeSubst.typeVarsList, List.mem_append]
        exact Or.inr (ih htail name hname)

/-- Every child of an insulated expression is insulated in the same public
scope. -/
theorem TypeVariablesInsulated.expression_child
    {publicNames : List String} {types : List Atom} {type : Atom}
    (insulated : TypeVariablesInsulated publicNames (.expression types))
    (htype : type ∈ types) :
    TypeVariablesInsulated publicNames type := by
  intro name hname
  exact insulated name
    (typeVars_mem_typeVarsList_of_mem htype name hname)

private theorem forall_insulated_of_all_members
    {publicNames : List String} {types : List Atom}
    (hall : ∀ type ∈ types, TypeVariablesInsulated publicNames type) :
    List.Forall (TypeVariablesInsulated publicNames) types :=
  List.forall_iff_forall_mem.mpr hall

/-- An insulated function presentation insulates every argument and its
return in the same public scope. -/
theorem TypeVariablesInsulated.function_components
    {publicNames : List String} {functionType returnType : Atom}
    {argumentTypes : List Atom}
    (insulated : TypeVariablesInsulated publicNames functionType)
    (function : FunctionTypeRel functionType argumentTypes returnType) :
    List.Forall (TypeVariablesInsulated publicNames) argumentTypes ∧
      TypeVariablesInsulated publicNames returnType := by
  subst functionType
  constructor
  · apply forall_insulated_of_all_members
    intro argument hargument
    apply insulated.expression_child
    simp [hargument]
  · apply insulated.expression_child
    simp

/-- Observable equality for one ordered candidate position.  Published
candidates use literal equality; inferred candidates use insulated alpha
siblings. -/
def ObservedCandidateEqRel
    (publicNames : List String) (left right : Atom) : Prop :=
  left = right ∨
    ObservedTypeAlphaRel left right ∧
      TypeVariablesInsulated publicNames left ∧
      TypeVariablesInsulated publicNames right

@[refl] theorem ObservedCandidateEqRel.refl
    (publicNames : List String) (type : Atom) :
    ObservedCandidateEqRel publicNames type type :=
  Or.inl rfl

theorem ObservedCandidateEqRel.symm
    {publicNames : List String} {left right : Atom}
    (equiv : ObservedCandidateEqRel publicNames left right) :
    ObservedCandidateEqRel publicNames right left := by
  rcases equiv with rfl | ⟨alpha, hleft, hright⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨alpha.symm, hright, hleft⟩

/-- Pointwise alpha-exact equality of ordered candidate lists.  `Forall₂`
keeps order, length, and multiplicity explicit. -/
def ObservedCandidateListsEqRel
    (publicNames : List String) (left right : List Atom) : Prop :=
  List.Forall₂ (ObservedCandidateEqRel publicNames) left right

theorem ObservedCandidateListsEqRel.refl
    (publicNames : List String) : ∀ types : List Atom,
    ObservedCandidateListsEqRel publicNames types types := by
  intro types
  induction types with
  | nil => exact List.Forall₂.nil
  | cons type types ih =>
      exact List.Forall₂.cons
        (ObservedCandidateEqRel.refl publicNames type) ih

theorem ObservedCandidateListsEqRel.symm
    {publicNames : List String} {left right : List Atom}
    (equiv : ObservedCandidateListsEqRel publicNames left right) :
    ObservedCandidateListsEqRel publicNames right left := by
  induction equiv with
  | nil => exact List.Forall₂.nil
  | cons head tail ih =>
      exact List.Forall₂.cons head.symm ih

theorem ObservedCandidateListsEqRel.length_eq
    {publicNames : List String} {left right : List Atom}
    (equiv : ObservedCandidateListsEqRel publicNames left right) :
    left.length = right.length := by
  induction equiv with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-! ## Package presentation boundary -/

/-- One exact package derivation together with the ordered atoms it presents
to evaluator consumers.  Keeping the package witness private prevents later
rules from confusing an inferred atom with evidence detached from its local
type theory. -/
def PackagesPresent
    (space : Space) (atom : Atom) (packages : List TypePackage)
    (observed : List Atom) : Prop :=
  RuntimeTypePackagesRel space atom packages ∧
    observedTypes packages = observed

/-- The ordered runtime type observation exposed to evaluator consumers.
Alpha-varying package witnesses are existential; consumers of negative
premises must first establish invariance under `ObservedCandidateListsEqRel`.
-/
def RuntimeTypesOfRel
    (space : Space) (atom : Atom) (observed : List Atom) : Prop :=
  ∃ packages, PackagesPresent space atom packages observed

theorem PackagesPresent.nonempty
    {space : Space} {atom : Atom} {packages : List TypePackage}
    {observed : List Atom}
    (present : PackagesPresent space atom packages observed) :
    observed ≠ [] := by
  rcases present with ⟨packagesRel, rfl⟩
  intro hempty
  apply packagesRel.nonempty
  simpa [observedTypes] using hempty

theorem RuntimeTypesOfRel.nonempty
    {space : Space} {atom : Atom} {observed : List Atom}
    (types : RuntimeTypesOfRel space atom observed) :
    observed ≠ [] := by
  rcases types with ⟨packages, present⟩
  exact present.nonempty

/-! ## Arrow-skeleton invariance -/

/-- Renaming preserves and reflects the published arrow decomposition. -/
theorem functionTypeRel_renameHumanTypeVars_iff
    (rename : String → String) (source : Atom)
    (argumentTypes : List Atom) (returnType : Atom) :
    FunctionTypeRel (renameHumanTypeVars rename source)
        argumentTypes returnType ↔
      ∃ sourceArguments sourceReturn,
        FunctionTypeRel source sourceArguments sourceReturn ∧
        argumentTypes =
          sourceArguments.map (renameHumanTypeVars rename) ∧
        returnType = renameHumanTypeVars rename sourceReturn := by
  constructor
  · intro hfunction
    cases source with
    | symbol name =>
        simp [FunctionTypeRel, renameHumanTypeVars] at hfunction
    | var name =>
        simp [FunctionTypeRel, renameHumanTypeVars] at hfunction
    | grounded value =>
        simp [FunctionTypeRel, renameHumanTypeVars] at hfunction
    | expression atoms =>
        simp only [FunctionTypeRel, renameHumanTypeVars,
          Atom.expression.injEq] at hfunction
        obtain ⟨sourceHead, sourceTail, hatoms, hhead, htail⟩ :=
          List.map_eq_cons_iff.mp hfunction
        have hsourceHead : sourceHead = .symbol "->" := by
          cases sourceHead <;>
            simp [renameHumanTypeVars] at hhead ⊢
          exact hhead
        subst sourceHead
        obtain ⟨sourceArguments, sourceLast, hsourceTail,
            harguments, hlast⟩ :=
          List.map_eq_append_iff.mp htail
        obtain ⟨sourceReturn, hsourceLast, hreturn⟩ :=
          List.map_eq_singleton_iff.mp hlast
        subst sourceTail
        subst sourceLast
        refine ⟨sourceArguments, sourceReturn, ?_,
          harguments.symm, ?_⟩
        · simp [FunctionTypeRel, hatoms]
        · simpa using hreturn.symm
  · rintro ⟨sourceArguments, sourceReturn, hsource, rfl, rfl⟩
    simp only [FunctionTypeRel] at hsource ⊢
    rw [hsource]
    simp [renameHumanTypeVars]

private theorem mapped_types_are_alpha_siblings
    (leftRename rightRename : String → String)
    (leftInjective : Function.Injective leftRename)
    (rightInjective : Function.Injective rightRename) :
    ∀ sourceTypes : List Atom,
      List.Forall₂ ObservedTypeAlphaRel
        (sourceTypes.map (renameHumanTypeVars leftRename))
        (sourceTypes.map (renameHumanTypeVars rightRename)) := by
  intro sourceTypes
  induction sourceTypes with
  | nil => exact List.Forall₂.nil
  | cons source sources ih =>
      apply List.Forall₂.cons
      · exact ⟨source,
          ⟨leftRename, leftInjective, rfl⟩,
          ⟨rightRename, rightInjective, rfl⟩⟩
      · exact ih

/-- Alpha siblings expose the same arrow head and arity, with pointwise
alpha-sibling argument and return components. -/
theorem ObservedTypeAlphaRel.function_skeleton
    {left right : Atom} {leftArguments : List Atom}
    {leftReturn : Atom}
    (alpha : ObservedTypeAlphaRel left right)
    (leftFunction :
      FunctionTypeRel left leftArguments leftReturn) :
    ∃ rightArguments rightReturn,
      FunctionTypeRel right rightArguments rightReturn ∧
      List.Forall₂ ObservedTypeAlphaRel
        leftArguments rightArguments ∧
      ObservedTypeAlphaRel leftReturn rightReturn := by
  rcases alpha with
    ⟨source,
      ⟨leftRename, leftInjective, hleft⟩,
      ⟨rightRename, rightInjective, hright⟩⟩
  rw [hleft] at leftFunction
  obtain ⟨sourceArguments, sourceReturn, sourceFunction,
      hleftArguments, hleftReturn⟩ :=
    (functionTypeRel_renameHumanTypeVars_iff
      leftRename source leftArguments leftReturn).mp leftFunction
  subst leftArguments
  subst leftReturn
  refine ⟨sourceArguments.map (renameHumanTypeVars rightRename),
    renameHumanTypeVars rightRename sourceReturn, ?_, ?_, ?_⟩
  · rw [hright]
    exact (functionTypeRel_renameHumanTypeVars_iff
      rightRename source _ _).mpr
        ⟨sourceArguments, sourceReturn, sourceFunction, rfl, rfl⟩
  · exact mapped_types_are_alpha_siblings
      leftRename rightRename leftInjective rightInjective sourceArguments
  · exact ⟨sourceReturn,
      ⟨leftRename, leftInjective, rfl⟩,
      ⟨rightRename, rightInjective, rfl⟩⟩

private theorem mapped_alpha_candidates
    {publicNames : List String}
    {leftTypes rightTypes : List Atom}
    (alpha : List.Forall₂ ObservedTypeAlphaRel leftTypes rightTypes)
    (leftInsulated :
      List.Forall (TypeVariablesInsulated publicNames) leftTypes)
    (rightInsulated :
      List.Forall (TypeVariablesInsulated publicNames) rightTypes) :
    List.Forall₂ (ObservedCandidateEqRel publicNames)
      leftTypes rightTypes := by
  induction alpha with
  | nil => exact List.Forall₂.nil
  | cons head tail ih =>
      have leftParts :=
        (List.forall_cons _ _ _).mp leftInsulated
      have rightParts :=
        (List.forall_cons _ _ _).mp rightInsulated
      exact List.Forall₂.cons
        (Or.inr ⟨head, leftParts.1, rightParts.1⟩)
        (ih leftParts.2 rightParts.2)

/-- Candidate equality preserves every piece of arrow structure consumed by
applicability: head, arity, ordered arguments, and return.  Private leaves
remain alpha-exact and insulated. -/
theorem ObservedCandidateEqRel.function_skeleton
    {publicNames : List String} {left right : Atom}
    {leftArguments : List Atom} {leftReturn : Atom}
    (equiv : ObservedCandidateEqRel publicNames left right)
    (leftFunction : FunctionTypeRel left leftArguments leftReturn) :
    ∃ rightArguments rightReturn,
      FunctionTypeRel right rightArguments rightReturn ∧
      List.Forall₂ (ObservedCandidateEqRel publicNames)
        leftArguments rightArguments ∧
      ObservedCandidateEqRel publicNames leftReturn rightReturn := by
  rcases equiv with rfl | ⟨alpha, leftInsulated, rightInsulated⟩
  · exact ⟨leftArguments, leftReturn, leftFunction,
      ObservedCandidateListsEqRel.refl publicNames leftArguments,
      ObservedCandidateEqRel.refl publicNames leftReturn⟩
  · obtain ⟨rightArguments, rightReturn, rightFunction,
      argumentsAlpha, returnAlpha⟩ :=
      alpha.function_skeleton leftFunction
    obtain ⟨leftArgumentsInsulated, leftReturnInsulated⟩ :=
      leftInsulated.function_components leftFunction
    obtain ⟨rightArgumentsInsulated, rightReturnInsulated⟩ :=
      rightInsulated.function_components rightFunction
    exact ⟨rightArguments, rightReturn, rightFunction,
      mapped_alpha_candidates argumentsAlpha
        leftArgumentsInsulated rightArgumentsInsulated,
      Or.inr ⟨returnAlpha, leftReturnInsulated,
        rightReturnInsulated⟩⟩

/-! ## Boundary examples -/

/-- Positive: private variable spellings are alpha siblings. -/
theorem private_variables_alpha_siblings :
    ObservedTypeAlphaRel (.var "alpha#t") (.var "beta#t") := by
  refine ⟨.var "t", ?_, ?_⟩
  · refine ⟨fun name => "alpha#" ++ name, ?_, ?_⟩
    intro left right heq
    apply String.toList_injective
    have hlists := congrArg String.toList heq
    simp only [String.toList_append] at hlists
    exact List.append_right_injective "alpha#".toList hlists
    simp [renameHumanTypeVars]
  · refine ⟨fun name => "beta#" ++ name, ?_, ?_⟩
    intro left right heq
    apply String.toList_injective
    have hlists := congrArg String.toList heq
    simp only [String.toList_append] at hlists
    exact List.append_right_injective "beta#".toList hlists
    simp [renameHumanTypeVars]

/-- Negative: alpha variation never changes a literal type symbol. -/
theorem distinct_symbols_not_alpha_siblings :
    ¬ObservedTypeAlphaRel (.symbol "A") (.symbol "B") := by
  rintro ⟨source,
    ⟨leftRename, _, hleft⟩,
    ⟨rightRename, _, hright⟩⟩
  cases source with
  | symbol name =>
      simp [renameHumanTypeVars] at hleft hright
      have hAB : ("A" : String) = "B" := hleft.trans hright.symm
      simp at hAB
  | var name => simp [renameHumanTypeVars] at hleft
  | grounded value => simp [renameHumanTypeVars] at hleft
  | expression atoms => simp [renameHumanTypeVars] at hleft

end Mettapedia.Languages.MeTTa.HE.HumanTypePresentationAlpha
