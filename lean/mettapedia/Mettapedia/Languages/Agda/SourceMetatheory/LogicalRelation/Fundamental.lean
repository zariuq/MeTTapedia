import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityComputation

/-!
The fundamental lemma for all eighteen constructors of the frozen finite-Set
and relevant-Pi source. The mutual induction returns context validity and
the complete substitution-validity predicates; all constructor clauses were
proved for the concrete relation in the preceding modules.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification

mutual
  theorem fundamentalContext {Γ : RawContext n} (d : FormCtx Γ) : ValidContext Γ :=
    match d with
    | .nil => .nil
    | .snoc context domain => .snoc (fundamentalContext context) (fundamentalType domain).2
  termination_by structural d

  theorem fundamentalType {Γ : RawContext n} {A : Ty n} (d : FormTy Γ A) :
      ValidContext Γ ∧ ValidType Γ A :=
    match d with
    | .ofTyping typed => ⟨(fundamentalTyping typed).1, .ofTyping (fundamentalTyping typed).2⟩
  termination_by structural d

  theorem fundamentalTyping {Γ : RawContext n} {t : Term n} {A : Ty n} (d : Typing Γ t A) :
      ValidContext Γ ∧ ValidTerm Γ t A :=
    match d with
    | .sort k context => ⟨fundamentalContext context, .sort context k⟩
    | .var i context => ⟨fundamentalContext context, .var (fundamentalContext context) i⟩
    | .pi domain codomain =>
        ⟨(fundamentalType domain).1, ValidTerm.pi (fundamentalType domain).2 (fundamentalType codomain).2⟩
    | .lam domain codomain body =>
        ⟨(fundamentalType domain).1,
          .lam (fundamentalType domain).2 (fundamentalType codomain).2 (fundamentalTyping body).2⟩
    | .app function argument =>
        ⟨(fundamentalTyping function).1, (fundamentalTyping function).2.app (fundamentalTyping argument).2⟩
    | .conv typed equal =>
        ⟨(fundamentalTyping typed).1, (fundamentalTyping typed).2.conv (fundamentalTypeEquality equal).2⟩
  termination_by structural d

  theorem fundamentalTypeEquality {Γ : RawContext n} {A B : Ty n} (d : TypeEq Γ A B) :
      ValidContext Γ ∧ ValidTypeEq Γ A B :=
    match d with
    | .atSort equal => ⟨(fundamentalTermEquality equal).1, .atSort (fundamentalTermEquality equal).2⟩
  termination_by structural d

  theorem fundamentalTermEquality {Γ : RawContext n} {t u : Term n} {A : Ty n}
      (d : TermEq Γ t u A) : ValidContext Γ ∧ ValidTermEq Γ t u A :=
    match d with
    | .refl typed => ⟨(fundamentalTyping typed).1, .refl (fundamentalTyping typed).2⟩
    | .symm equal => ⟨(fundamentalTermEquality equal).1, (fundamentalTermEquality equal).2.symm⟩
    | .trans first second =>
        ⟨(fundamentalTermEquality first).1,
          (fundamentalTermEquality first).2.trans (fundamentalTermEquality second).2⟩
    | .conv equal types =>
        ⟨(fundamentalTermEquality equal).1,
          (fundamentalTermEquality equal).2.conv (fundamentalTypeEquality types).2⟩
    | .piCong domain domains codomains =>
        ⟨(fundamentalType domain).1,
          .piCong (fundamentalTypeEquality domains).2 (fundamentalTypeEquality codomains).2⟩
    | .appCong functions arguments =>
        ⟨(fundamentalTermEquality functions).1,
          .appCong (fundamentalTermEquality functions).2 (fundamentalTermEquality arguments).2⟩
    | .beta domain codomain body argument =>
        ⟨(fundamentalType domain).1,
          .beta (fundamentalType domain).2 (fundamentalType codomain).2
            (fundamentalTyping body).2 (fundamentalTyping argument).2⟩
    | .eta domain codomain left right pointwise =>
        ⟨(fundamentalType domain).1,
          .eta (fundamentalType domain).2 (fundamentalType codomain).2
            (fundamentalTyping left).2 (fundamentalTyping right).2 (fundamentalTermEquality pointwise).2⟩
  termination_by structural d
end

theorem formedTypeRelated {Γ : RawContext n} {A : Ty n} (d : FormTy Γ A) :
    LogRel A.level Γ A (annotatedPack Γ A) := by
  have valid := fundamentalType d
  simpa only [Ty.subst_id] using valid.2.reducible valid.1.identity

theorem typedTermMember {Γ : RawContext n} {t : Term n} {A : Ty n} (d : Typing Γ t A) :
    LogRel A.level Γ A (annotatedPack Γ A) ∧ (annotatedPack Γ A).redTm t := by
  have valid := fundamentalTyping d
  constructor
  · simpa only [Ty.subst_id] using valid.2.type.reducible valid.1.identity
  · simpa only [Ty.subst_id, Term.subst_id] using valid.2.member valid.1.identity

theorem equalTypesRelated {Γ : RawContext n} {A B : Ty n} (d : TypeEq Γ A B) :
    LogRel A.level Γ A (annotatedPack Γ A) ∧ (annotatedPack Γ A).eqTy B := by
  have valid := fundamentalTypeEquality d
  constructor
  · simpa only [Ty.subst_id] using valid.2.left.reducible valid.1.identity
  · simpa only [Ty.subst_id] using valid.2.equal valid.1.identity

theorem equalTermsRelated {Γ : RawContext n} {t u : Term n} {A : Ty n} (d : TermEq Γ t u A) :
    LogRel A.level Γ A (annotatedPack Γ A) ∧ (annotatedPack Γ A).eqTm t u := by
  have valid := fundamentalTermEquality d
  constructor
  · simpa only [Ty.subst_id] using valid.2.left.type.reducible valid.1.identity
  · simpa only [Ty.subst_id, Term.subst_id] using valid.2.equal valid.1.identity

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
