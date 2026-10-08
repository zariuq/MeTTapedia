import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualComprehensionSyntax

/-!
# Dependent external comprehension controls

A primitive family receives a function as its parameter. Its annotations at
the function and its eta expansion are different syntax but generated-equal.
The dependent witness is retyped between those annotations and survives actual
quotient pairing. An older variable shifts under the newly added binder.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.ContextualControls

open _root_.CategoryTheory Contextual

inductive TypeSymbol where
  | ground
  | indexed

abbrev symbols : Symbols where
  TypeSymbol := TypeSymbol
  TermSymbol := Empty
  typeArity
    | .ground => 0
    | .indexed => 1
  termArity := Empty.elim

def ground (n : Nat) : TypeExpr symbols n := .family .ground Fin.elim0
def functionType (n : Nat) : TypeExpr symbols n := .pi (ground n) (ground (n + 1))

abbrev signature : Signature symbols where
  typeRank
    | .ground => 0
    | .indexed => 1
  termRank := Empty.elim
  typeParameters
    | .ground => .nil
    | .indexed => .snoc .nil (functionType 0)
  termParameters := fun symbol => Empty.elim symbol
  termResult := fun symbol => Empty.elim symbol
  typeParameters_before := by
    intro symbol
    cases symbol <;>
      simp [ContextExpr.before, TypeExpr.before, ground, functionType, symbols]
  termParameters_before := by intro symbol; exact Empty.elim symbol
  termResult_before := by intro symbol; exact Empty.elim symbol

@[simp] theorem ground_rename {n m : Nat} (mapping : Renaming n m) :
    (ground n).rename mapping = ground m := by
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.ground)
  funext position
  exact Fin.elim0 position

@[simp] theorem ground_substitute {n m : Nat} (substitution : Substitution symbols n m) :
    (ground n).substitute substitution = ground m := by
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.ground)
  funext position
  exact Fin.elim0 position

@[simp] theorem functionType_rename {n m : Nat} (mapping : Renaming n m) :
    (functionType n).rename mapping = functionType m := by
  change TypeExpr.pi ((ground n).rename mapping) ((ground (n + 1)).rename (liftRenaming mapping)) = _
  rw [ground_rename, ground_rename]
  rfl

@[simp] theorem functionType_substitute {n m : Nat} (substitution : Substitution symbols n m) :
    (functionType n).substitute substitution = functionType m := by
  change TypeExpr.pi ((ground n).substitute substitution)
    ((ground (n + 1)).substitute (liftSubstitution substitution)) = _
  rw [ground_substitute, ground_substitute]
  rfl

theorem ground_formed {n : Nat} {context : ContextExpr symbols n} (formed : Formed signature context) :
    Holds signature (.type context (ground n)) :=
  conclude (.typeFamily context TypeSymbol.ground Fin.elim0)
    ⟨formed.judgment, conclude .contextNil trivial,
      conclude (.substitutionNil context) ⟨formed.judgment, trivial⟩, trivial⟩

theorem function_formed {n : Nat} {context : ContextExpr symbols n} (formed : Formed signature context) :
    Holds signature (.type context (functionType n)) :=
  conclude (.piFormation context (ground n) (ground (n + 1)))
    ⟨ground_formed formed, ground_formed (.snoc formed (ground_formed formed)), trivial⟩

abbrev functionContext : Context signature :=
  ⟨1, .snoc .nil (functionType 0), .snoc .nil (function_formed .nil)⟩

def suppliedFunction : TermExpr symbols 1 := .var 0
def expandedFunction : TermExpr symbols 1 :=
  .lam (ground 1) (ground 2) (.app (ground 2) (ground 3) (.var 1) (.var 0))

theorem supplied_typed : Holds signature (.term functionContext.raw suppliedFunction (functionType 1)) := by
  have entry := conclude (.variable functionContext.raw (0 : Fin 1)) ⟨functionContext.formed.judgment, trivial⟩
  simpa only [RuleCode.conclusion, functionContext, ContextExpr.lookup_zero, functionType_rename,
    suppliedFunction] using entry

theorem expanded_typed : Holds signature (.term functionContext.raw expandedFunction (functionType 1)) := by
  let extended := ContextExpr.snoc functionContext.raw (ground 1)
  have formed : Formed signature extended := .snoc functionContext.formed (ground_formed functionContext.formed)
  have older := conclude (.variable extended (1 : Fin 2)) ⟨formed.judgment, trivial⟩
  have olderTyped : Holds signature (.term extended (.var 1) (functionType 2)) := by
    change Holds signature (.term extended (.var 1)
      (((functionType 0).rename Fin.succ).rename Fin.succ)) at older
    simpa only [functionType_rename] using older
  have newest := conclude (.variable extended (0 : Fin 2)) ⟨formed.judgment, trivial⟩
  have newestTyped : Holds signature (.term extended (.var 0) (ground 2)) := by
    change Holds signature (.term extended (.var 0) ((ground 1).rename Fin.succ)) at newest
    simpa only [ground_rename] using newest
  have evaluated := conclude (.application extended (ground 2) (ground 3) (.var 1) (.var 0))
    ⟨ground_formed formed, ground_formed (.snoc formed (ground_formed formed)), olderTyped, newestTyped, trivial⟩
  have bodyTyped : Holds signature (.term extended (.app (ground 2) (ground 3) (.var 1) (.var 0))
      (ground 2)) := by simpa only [RuleCode.conclusion, ground_substitute] using evaluated
  exact conclude (.lambda functionContext.raw (ground 1) (ground 2)
    (.app (ground 2) (ground 3) (.var 1) (.var 0)))
    ⟨ground_formed functionContext.formed, ground_formed formed, bodyTyped, trivial⟩

set_option backward.isDefEq.respectTransparency false in
theorem function_eta : Holds signature
    (.termEq functionContext.raw expandedFunction suppliedFunction (functionType 1)) := by
  have eta := conclude (.piEta functionContext.raw (ground 1) (ground 2) suppliedFunction)
    ⟨ground_formed functionContext.formed,
      ground_formed (.snoc functionContext.formed (ground_formed functionContext.formed)), supplied_typed, trivial⟩
  simpa only [RuleCode.conclusion, ground_rename, suppliedFunction, expandedFunction,
    functionType, TermExpr.rename, Fin.succ_zero_eq_one] using eta

theorem different_function_syntax : expandedFunction ≠ suppliedFunction := by
  intro same
  cases same

def firstArguments : Substitution symbols 1 1 := extendSubstitution Fin.elim0 suppliedFunction
def secondArguments : Substitution symbols 1 1 := extendSubstitution Fin.elim0 expandedFunction

theorem first_substitution : Holds signature
    (.substitution functionContext.raw functionContext.raw firstArguments) := by
  have head : Holds signature (.term functionContext.raw suppliedFunction
      ((functionType 0).substitute Fin.elim0)) := by simpa only [functionType_substitute] using supplied_typed
  exact conclude (.substitutionExtend functionContext.raw .nil (functionType 0) Fin.elim0 suppliedFunction)
    ⟨conclude (.substitutionNil functionContext.raw) ⟨functionContext.formed.judgment, trivial⟩,
      function_formed .nil, head, trivial⟩

theorem second_substitution : Holds signature
    (.substitution functionContext.raw functionContext.raw secondArguments) := by
  have head : Holds signature (.term functionContext.raw expandedFunction
      ((functionType 0).substitute Fin.elim0)) := by simpa only [functionType_substitute] using expanded_typed
  exact conclude (.substitutionExtend functionContext.raw .nil (functionType 0) Fin.elim0 expandedFunction)
    ⟨conclude (.substitutionNil functionContext.raw) ⟨functionContext.formed.judgment, trivial⟩,
      function_formed .nil, head, trivial⟩

theorem arguments_equal : Holds signature
    (.substitutionEq functionContext.raw functionContext.raw firstArguments secondArguments) := by
  have head : Holds signature (.termEq functionContext.raw suppliedFunction expandedFunction
      ((functionType 0).substitute Fin.elim0)) := by
    simpa only [functionType_substitute] using termEquality_symm function_eta
  have second : Holds signature (.term functionContext.raw expandedFunction
      ((functionType 0).substitute Fin.elim0)) := by simpa only [functionType_substitute] using expanded_typed
  exact conclude (.substitutionExtendEquality functionContext.raw .nil (functionType 0)
    Fin.elim0 Fin.elim0 suppliedFunction expandedFunction)
    ⟨substitutionEquality_refl
      (conclude (.substitutionNil functionContext.raw) ⟨functionContext.formed.judgment, trivial⟩),
      function_formed .nil, head, second, trivial⟩

def firstFamily : TypeOver functionContext :=
  ⟨.family .indexed firstArguments, conclude (.typeFamily functionContext.raw TypeSymbol.indexed firstArguments)
    ⟨functionContext.formed.judgment, functionContext.formed.judgment, first_substitution, trivial⟩⟩

def secondFamily : TypeOver functionContext :=
  ⟨.family .indexed secondArguments, conclude (.typeFamily functionContext.raw TypeSymbol.indexed secondArguments)
    ⟨functionContext.formed.judgment, functionContext.formed.judgment, second_substitution, trivial⟩⟩

theorem annotations_equal : Holds signature (.typeEq functionContext.raw firstFamily.code secondFamily.code) :=
  conclude (.familyCongruence functionContext.raw TypeSymbol.indexed firstArguments secondArguments)
    ⟨functionContext.formed.judgment, arguments_equal, trivial⟩

theorem different_annotation_syntax : firstFamily.code ≠ secondFamily.code := by
  intro same
  have arguments : firstArguments = secondArguments := eq_of_heq (TypeExpr.family.inj same |>.2)
  have functions : suppliedFunction = expandedFunction := congrFun arguments 0
  exact different_function_syntax functions.symm

abbrev witnessContext : Context signature := extend functionContext firstFamily
abbrev olderProjection : witnessContext ⟶ functionContext := projectionHom functionContext firstFamily
abbrev firstAnnotation : TypeOver witnessContext := firstFamily.reindex olderProjection
abbrev secondAnnotation : TypeOver witnessContext := secondFamily.reindex olderProjection
def witness : Term witnessContext firstAnnotation := newest functionContext firstFamily

theorem annotations_substituted : Holds signature
    (.typeEq witnessContext.raw firstAnnotation.code secondAnnotation.code) :=
  reindex_typeEquality annotations_equal olderProjection

def convertedWitness : Term witnessContext secondAnnotation :=
  witness.convertType secondAnnotation annotations_substituted

theorem dependent_annotation_retained : QType.mk firstAnnotation = QType.mk secondAnnotation :=
  (QType.mk_eq_iff _ _).mpr annotations_substituted

theorem converted_witness_retained : QTerm.mk convertedWitness = QTerm.mk witness :=
  QTerm.mk_convertType witness secondAnnotation annotations_substituted

theorem projection_shifts_parameter : firstAnnotation.code = .family .indexed (fun _ => .var (1 : Fin 2)) := by
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.indexed)
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ prior => exact Fin.elim0 prior

theorem omitted_parameter_shift : firstAnnotation.code ≠ (.family .indexed (fun _ => .var (0 : Fin 2))) := by
  intro same
  have arguments := eq_of_heq (TypeExpr.family.inj same |>.2)
  have values := congrFun arguments 0
  have indices : (1 : Fin 2) = 0 := TermExpr.var.inj values
  exact (by decide : (1 : Fin 2) ≠ 0) indices

def nativeWitness : QuotientCwf.Tm ((quotientProjection signature).obj witnessContext)
    (QuotientCwf.tySub (QType.mk secondFamily) (QuotientCwf.project olderProjection)) :=
  ⟨QTerm.mk witness, dependent_annotation_retained⟩

theorem pairing_base :
    QuotientCwf.pair (QuotientCwf.project olderProjection) (QType.mk secondFamily) nativeWitness ≫
      QuotientCwf.wk (QType.mk secondFamily) = QuotientCwf.project olderProjection :=
  QuotientCwf.wk_pair _ _ _

theorem pairing_value :
    (QuotientCwf.tmSub (QuotientCwf.vz (QType.mk secondFamily))
      (QuotientCwf.pair (QuotientCwf.project olderProjection) (QType.mk secondFamily) nativeWitness)).val =
      QTerm.mk witness := QuotientCwf.vz_pair_value _ _ _

theorem selected_annotation_conversion :
    QTerm.mk (QuotientCwf.termRepresentative secondAnnotation (QTerm.mk witness)
      dependent_annotation_retained) = QTerm.mk witness :=
  QuotientCwf.termRepresentative_class _ _ _

def annotationExtensionIso : extend functionContext firstFamily ≅ extend functionContext secondFamily :=
  extensionComparison firstFamily secondFamily annotations_equal

theorem extension_changes_annotation :
    (extend functionContext firstFamily).raw ≠ (extend functionContext secondFamily).raw := by
  intro same
  have codes : firstFamily.code = secondFamily.code := ContextExpr.snoc.inj same |>.2
  exact different_annotation_syntax codes

theorem extension_keeps_variables : annotationExtensionIso.hom.substitution = TermExpr.var :=
  extensionComparison_hom_substitution _ _ _

theorem extension_keeps_projection :
    annotationExtensionIso.hom ≫ projectionHom functionContext secondFamily = olderProjection :=
  extensionComparison_projection _ _ _

theorem supplied_extension_matches_selected :
    (QuotientCwf.extPresentation functionContext secondFamily).hom ≫
      QuotientCwf.project (projectionHom functionContext secondFamily) =
      QuotientCwf.wk (QType.mk secondFamily) :=
  QuotientCwf.extPresentation_projection _ _

theorem selected_section_retains_witness :
    (QuotientCwf.tmSub (QuotientCwf.vz (QType.mk secondAnnotation))
      (Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf signature)
        (⟨QTerm.mk convertedWitness, rfl⟩ :
          QuotientCwf.Tm ((quotientProjection signature).obj witnessContext) (QType.mk secondAnnotation)))).val =
      QTerm.mk witness :=
  (QuotientComprehensionSyntax.selfExtend_value _).trans converted_witness_retained

theorem lifted_older_parameter :
    (QuotientComprehensionSyntax.rawLift olderProjection secondFamily).substitution (1 : Fin 2) =
      .var (2 : Fin 3) := by
  rw [QuotientComprehensionSyntax.rawLift_substitution]
  rfl

theorem omitted_lifted_shift :
    (QuotientComprehensionSyntax.rawLift olderProjection secondFamily).substitution (1 : Fin 2) ≠
      .var (1 : Fin 3) := by
  rw [lifted_older_parameter]
  intro same
  exact (by decide : (2 : Fin 3) ≠ 1) (TermExpr.var.inj same)

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.ContextualControls
