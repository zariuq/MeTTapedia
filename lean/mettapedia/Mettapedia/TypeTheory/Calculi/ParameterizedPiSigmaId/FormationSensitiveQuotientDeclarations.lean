import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientInterpretation

/-! # Declared constants in the formed quotient

The construction is parameterized by the declared rules and uses the existing
formation, substitution and conversion judgments. Concrete language controls
are separate consumers, not premises of these laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientDeclarations

open _root_.CategoryTheory Declaration FormationSensitive QuotientInterpretation

variable {Head : Type} {rules : Rules Head}

theorem liftClosed_at_empty (term : Tm Head 0) : (liftClosed term : Tm Head 0) = term := by
  have emptyRenaming : (Fin.elim0 : Ren 0 0) = id := by
    funext index
    exact Fin.elim0 index
  change rename Fin.elim0 term = term
  rw [emptyRenaming]
  exact rename_id term

/-- The real constant rule still requires formation of its declared type. -/
def closedConstant (name : DeclName) (type : TypeOver (empty rules))
    (known : rules.constantType name = some type.code) : Term (empty rules) type where
  code := .const name
  typed := (liftClosed_at_empty type.code) ▸
    (Typing.const (R := rules) (Γ := .nil) known type.formed type.universeWitness)

theorem closed_type_meaning (type : TypeOver (empty rules)) :
    TypeMeaning (empty rules) type.code (QType.mk type) := type_meaning _ _

theorem closed_constant_meaning (name : DeclName) (type : TypeOver (empty rules))
    (known : rules.constantType name = some type.code) :
    TermMeaning (empty rules) (.const name) type.code (QType.mk type)
      (TermFibre.mk (closedConstant name type known)) :=
  term_meaning (empty rules) (closedConstant name type known)

def typeIn (context : Context rules) (type : TypeOver (empty rules)) : TypeOver context :=
  type.reindex (toEmpty context)

def constantIn (context : Context rules) (name : DeclName) (type : TypeOver (empty rules))
    (known : rules.constantType name = some type.code) : Term context (typeIn context type) :=
  (closedConstant name type known).reindex (toEmpty context)

theorem typeIn_code (context : Context rules) (type : TypeOver (empty rules)) :
    (typeIn context type).code = liftClosed type.code := by
  have substitution : (toEmpty context).substitution = renSub Fin.elim0 := by
    funext index
    exact Fin.elim0 index
  exact (congrArg (fun replacement : Sub Head 0 context.arity => subst replacement type.code)
    substitution).trans (subst_renSub Fin.elim0 type.code)

theorem constantIn_code (context : Context rules) (name : DeclName)
    (type : TypeOver (empty rules)) (known : rules.constantType name = some type.code) :
    (constantIn context name type known).code = .const name := rfl

theorem caller_type_meaning (context : Context rules) (type : TypeOver (empty rules)) :
    TypeMeaning context (liftClosed type.code) (QType.mk (typeIn context type)) :=
  ⟨typeIn context type, typeIn_code context type, rfl⟩

theorem caller_constant_meaning (context : Context rules) (name : DeclName)
    (type : TypeOver (empty rules)) (known : rules.constantType name = some type.code) :
    TermMeaning context (.const name) (liftClosed type.code) (QType.mk (typeIn context type))
      (TermFibre.mk (constantIn context name type known)) :=
  ⟨typeIn context type, typeIn_code context type,
    constantIn context name type known, rfl, rfl, rfl⟩

theorem caller_constant_judgment (context : Context rules) (name : DeclName)
    (type : TypeOver (empty rules)) (known : rules.constantType name = some type.code) :
    Judgment rules context.raw (.const name) (liftClosed type.code) := by
  have admitted := (constantIn context name type known).judgment
  rw [constantIn_code, typeIn_code] at admitted
  exact admitted

theorem typeIn_substitution {source target : Context rules}
    (morphism : source ⟶ target) (type : TypeOver (empty rules)) :
    (typeIn target type).reindex morphism = typeIn source type := by
  change (type.reindex (toEmpty target)).reindex morphism = _
  rw [← TypeOver.reindex_comp, toEmpty_unique source (morphism ≫ toEmpty target)]
  rfl

/-- This equality retains the actual source code after the annotation
comparison. It is not a coherence premise of the interpretation. -/
theorem constantIn_substitution {source target : Context rules}
    (morphism : source ⟶ target) (name : DeclName) (type : TypeOver (empty rules))
    (known : rules.constantType name = some type.code) :
    ((constantIn target name type known).reindex morphism).cast
      (typeIn_substitution morphism type) = constantIn source name type known := by
  apply Term.ext
  rw [Term.cast_code]
  rfl

theorem caller_type_class_substitution {source target : Context rules}
    (morphism : source ⟶ target) (type : TypeOver (empty rules)) :
    QuotientCwf.tySub (QType.mk (typeIn target type)) (QuotientCwf.project morphism) =
      QType.mk (typeIn source type) :=
  congrArg QType.mk (typeIn_substitution morphism type)

theorem caller_constant_class_substitution {source target : Context rules}
    (morphism : source ⟶ target) (name : DeclName) (type : TypeOver (empty rules))
    (known : rules.constantType name = some type.code) :
    QuotientCwf.totalSub (QTerm.mk (constantIn target name type known))
      (QuotientCwf.project morphism) = QTerm.mk (constantIn source name type known) := by
  apply Quotient.sound
  constructor
  · change Conv rules.headEq ((typeIn target type).reindex morphism).code
      (typeIn source type).code rules.computation
    rw [typeIn_substitution]
    exact .refl _
  · exact .refl _

/-- Every semantic arrow licensed by the admitted substitution graph has
the same declaration action, not just a separately chosen weakening map. -/
theorem caller_substitution_meaning {source target : Context rules}
    {substitution : Sub Head target.arity source.arity}
    {semantic : (quotientProjection rules).obj source ⟶ (quotientProjection rules).obj target}
    (related : SubstitutionMeaning target source substitution semantic)
    (name : DeclName) (type : TypeOver (empty rules))
    (known : rules.constantType name = some type.code) :
    QuotientCwf.tySub (QType.mk (typeIn target type)) semantic = QType.mk (typeIn source type) ∧
      QuotientCwf.totalSub (QTerm.mk (constantIn target name type known)) semantic =
        QTerm.mk (constantIn source name type known) := by
  obtain ⟨typed, rfl⟩ := related
  exact ⟨caller_type_class_substitution ⟨substitution, typed⟩ type,
    caller_constant_class_substitution ⟨substitution, typed⟩ name type known⟩

/-- The graph pins the exact displayed annotation and constant meaning.
Different formation witnesses do not permit a changed semantic value. -/
theorem caller_meaning_iff (context : Context rules) (name : DeclName)
    (type : TypeOver (empty rules)) (known : rules.constantType name = some type.code)
    (semanticType : QType context) (value : TermFibre semanticType) :
    TermMeaning context (.const name) (liftClosed type.code) semanticType value ↔
      QType.mk (typeIn context type) = semanticType ∧
        QTerm.mk (constantIn context name type known) = value.val := by
  constructor
  · rintro ⟨actualType, sameType, actual, sameCode, typeClass, termClass⟩
    have types : QType.mk (typeIn context type) = QType.mk actualType := by
      apply Quotient.sound
      change Conv rules.headEq (typeIn context type).code actualType.code rules.computation
      rw [typeIn_code, sameType]
      exact .refl _
    refine ⟨types.trans typeClass, ?_⟩
    apply Eq.trans _ termClass
    apply Quotient.sound
    constructor
    · exact (QType.mk_eq_iff _ _).mp types
    · rw [constantIn_code, sameCode]
      exact .refl _
  · rintro ⟨typeClass, termClass⟩
    exact ⟨typeIn context type, typeIn_code context type,
      constantIn context name type known, rfl, typeClass, termClass⟩

theorem no_term_meaning_of_missing (context : Context rules) (name : DeclName)
    (missing : rules.constantType name = none) (annotation : Tm Head context.arity)
    (semanticType : QType context) (value : TermFibre semanticType) :
    ¬ TermMeaning context (.const name) annotation semanticType value := by
  rintro ⟨actualType, _, actual, sameCode, _, _⟩
  have typed := actual.typed
  rw [sameCode] at typed
  obtain ⟨declaredType, level, known, _, _⟩ := typed.constFormation
  rw [missing] at known
  cases known

theorem no_type_meaning_of_missing (context : Context rules) (name : DeclName)
    (missing : rules.constantType name = none) (semanticType : QType context) :
    ¬ TypeMeaning context (.const name) semanticType := by
  rintro ⟨actualType, sameCode, _⟩
  have typed := actualType.formed
  rw [sameCode] at typed
  obtain ⟨declaredType, level, known, _, _⟩ := typed.constFormation
  rw [missing] at known
  cases known

section Installation

variable (base : Rules Head) (signature : Signature Head)

/-- Exact entry lookup derives effective lookup only when the base has no
declaration at that name. The existing shadowing policy is unchanged. -/
def installedConstant (name : DeclName) (entry : Entry Head)
    (installed : signature.entries name = some entry)
    (fresh : base.constantType name = none)
    (type : TypeOver (empty (extendRules base signature))) (sameType : type.code = entry.type) :
    Term (empty (extendRules base signature)) type :=
  closedConstant name type (by
    rw [sameType]
    apply combinedType_of_signature base signature fresh
    simp only [Signature.typeOf?, installed, Option.map_some])

theorem installed_constant_meaning (name : DeclName) (entry : Entry Head)
    (installed : signature.entries name = some entry)
    (fresh : base.constantType name = none)
    (type : TypeOver (empty (extendRules base signature))) (sameType : type.code = entry.type) :
    TermMeaning (empty (extendRules base signature)) (.const name) entry.type (QType.mk type)
      (TermFibre.mk (installedConstant base signature name entry installed fresh type sameType)) :=
  ⟨type, sameType, installedConstant base signature name entry installed fresh type sameType,
    rfl, rfl, rfl⟩

/-- An installed definition is interpreted by its actual licensed delta
step only when its displayed body is independently admitted at that type. -/
theorem installed_value_class (name : DeclName) (type : TypeOver (empty (extendRules base signature)))
    (known : (extendRules base signature).constantType name = some type.code)
    (body : Term (empty (extendRules base signature)) type)
    (installed : signature.valueOf? name = some body.code) :
    QTerm.mk (closedConstant name type known) = QTerm.mk body := by
  apply Quotient.sound
  refine ⟨.refl _, ?_⟩
  have step : Step (extendRules base signature).headEq
      (.const name : Tm Head 0) (liftClosed body.code) (extendRules base signature).computation :=
    .root (.delta installed)
  exact .rel _ _ ((liftClosed_at_empty body.code) ▸ step)

end Installation


end FormationSensitiveContextual.QuotientDeclarations
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
