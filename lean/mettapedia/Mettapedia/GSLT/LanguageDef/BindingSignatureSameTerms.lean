import Mettapedia.GSLT.LanguageDef.BindingSignatureTransport

/-!
# Binding-signature transport across presentations with the same constructors

Two `LanguageDef` presentations can share authored constructor declarations
while differing in equations or rewrite rules. Their intrinsic binding
signatures then have a strict operator map, even when there is no structural
language morphism preserving the two rule inventories. This map transports
syntax and substitution only; it is not an operational simulation.
-/

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding

set_option autoImplicit false

/-- Change only the membership witness of an authored constructor. The
parameter scopes and every generic binding representation form remain the
same. No equations or rewrites are transported by this operation. -/
def Operator.ofSameTerms {source target : LanguageDef}
    (same : source.terms = target.terms) :
    {sort : TypeExpr} → Operator source sort → Operator target sort
  | _, .constructor rule member ordinary parameters =>
      .constructor rule (same ▸ member) ordinary parameters
  | _, .collectionConstructor rule member name kind element shape count =>
      .collectionConstructor rule (same ▸ member) name kind element shape count
  | _, .lambda domain codomain => .lambda domain codomain
  | _, .multiLambda domain codomain count => .multiLambda domain codomain count
  | _, .subst domain codomain => .subst domain codomain
  | _, .collection kind element count => .collection kind element count

/-- The constructor-level transport is reversible. The only proof data
changed is membership in the two definitionally equal term inventories. -/
theorem Operator.ofSameTerms_symm {source target : LanguageDef}
    (same : source.terms = target.terms)
    {sort : TypeExpr} (operator : Operator source sort) :
    Operator.ofSameTerms same.symm (Operator.ofSameTerms same operator) =
      operator := by
  cases operator <;> rfl

/-- A presentation change with identical `terms` induces a strict morphism
of the declaration-derived binding signatures. The `SigMor` term action and
its generic `map_bind` theorem apply, but rewrite preservation does not
follow from this morphism. -/
def signatureSameTerms {source target : LanguageDef}
    (same : source.terms = target.terms) :
    SigMor (signatureOf source) (signatureOf target) where
  sortMap := id
  opMap := Operator.ofSameTerms same
  carriesArity := by
    intro sort operator
    change (signatureOf target).arity (Operator.ofSameTerms same operator) =
      mapArities (fun sort => sort) ((signatureOf source).arity operator)
    rw [mapArities_id]
    cases operator <;> rfl

theorem signatureSameTerms_comp_ident {source target : LanguageDef}
    (same : source.terms = target.terms) :
    (signatureSameTerms same).comp (signatureSameTerms same.symm) =
      SigMor.ident (signatureOf source) := by
  unfold SigMor.comp signatureSameTerms SigMor.ident
  congr 1
  funext sort operator
  exact Operator.ofSameTerms_symm same operator

/-- Unlike the canonical `onTerm` action, a same-sort presentation change
can keep the context list literally fixed: variables themselves are shared. -/
def transportSameTerms {source target : LanguageDef}
    (same : source.terms = target.terms)
    {Γ : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf source) Γ sort) :
    Term (signatureOf target) Γ sort :=
  mapTerm (signatureSameTerms same) (fun _ position => position) term

/-- Back-and-forth transport preserves every intrinsic term over two
presentations with the same authored constructors. The proof transports the
dependent variable map along the signature-morphism equality explicitly. -/
theorem transportSameTerms_symm {source target : LanguageDef}
    (same : source.terms = target.terms)
    {Γ : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf source) Γ sort) :
    transportSameTerms same.symm (transportSameTerms same term) = term := by
  unfold transportSameTerms
  have composed := mapTerm_comp (signatureSameTerms same)
    (signatureSameTerms same.symm) (fun _ position => position)
    (fun _ position => position) term
  have asIdentity := mapTerm_heq_of_morphism_eq
    ((signatureSameTerms same).comp (signatureSameTerms same.symm))
    (SigMor.ident (signatureOf source))
    (signatureSameTerms_comp_ident same)
    (fun _ position => position) (fun _ position => position) (by rfl) term
  exact composed.trans (asIdentity.eq.trans
    ((mapTerm_ident (fun _ position => position) term).trans (rename_id term)))

/-- The context-preserving presentation equivalence respects the original
simultaneous substitution action, including arguments under binders. -/
theorem transportSameTerms_bind {source target : LanguageDef}
    (same : source.terms = target.terms)
    {Γ Δ : List TypeExpr} {sort : TypeExpr}
    (sigma : Sub (signatureOf source) Γ Δ)
    (term : Term (signatureOf source) Γ sort) :
    transportSameTerms same (bind sigma term) =
      bind (fun sort position => transportSameTerms same (sigma sort position))
        (transportSameTerms same term) := by
  unfold transportSameTerms
  exact mapTerm_bind (signatureSameTerms same)
    (fun _ position => position) (fun _ position => position) sigma
    (fun sort position => mapTerm (signatureSameTerms same)
      (fun _ position => position) (sigma sort position))
    (by intro sort position; rfl) term

private theorem eraseArguments_cast {language : LanguageDef}
    {first second : List (List TypeExpr × TypeExpr)} {Γ : List TypeExpr}
    (same : first = second)
    (arguments : Args (signatureOf language) first Γ) :
    eraseArguments (castArgsArity same arguments) =
      eraseArguments arguments := by
  cases same
  rfl

private theorem eraseConstructorArguments_eq
    {source target : LanguageDef} :
    ∀ {parameters : List TermParam}
      {arity : List (List TypeExpr × TypeExpr)}
      {Γ Δ : List TypeExpr}
      (scopes : ParameterScopes parameters arity)
      (first : Args (signatureOf source) arity Γ)
      (second : Args (signatureOf target) arity Δ),
      eraseArguments first = eraseArguments second →
      eraseConstructorArguments scopes first =
        eraseConstructorArguments scopes second
  | _, _, _, _, .nil, .nil, .nil, _ => rfl
  | _, _, _, _, .cons scope scopes, .cons firstHead firstTail,
      .cons secondHead secondTail, same => by
      have head := (List.cons.inj same).1
      have tail := (List.cons.inj same).2
      simp only [eraseConstructorArguments, head,
        eraseConstructorArguments_eq scopes firstTail secondTail tail]

private theorem erase_op_ofSameTerms
    {source target : LanguageDef}
    (same : source.terms = target.terms)
    {Γ Δ : List TypeExpr} {sort : TypeExpr}
    (operator : Operator source sort)
    (first : Args (signatureOf source) ((signatureOf source).arity operator) Γ)
    (second : Args (signatureOf target)
      ((signatureOf target).arity (Operator.ofSameTerms same operator)) Δ)
    (sameArguments : eraseArguments first = eraseArguments second) :
    erase (.op (Operator.ofSameTerms same operator) second) =
      erase (.op operator first) := by
  cases operator with
  | constructor rule member ordinary scopes =>
      exact congrArg (Pattern.apply rule.label)
        (eraseConstructorArguments_eq scopes first second sameArguments).symm
  | collectionConstructor =>
      exact congrArg (fun arguments => Pattern.collection _ arguments none)
        sameArguments.symm
  | lambda =>
      exact match first, second with
        | .cons firstBody .nil, .cons secondBody .nil => by
            have sameBody := (List.cons.inj sameArguments).1
            simpa [Operator.ofSameTerms, erase] using
              congrArg (Pattern.lambda none) sameBody.symm
  | multiLambda domain codomain count =>
      exact match first, second with
        | .cons firstBody .nil, .cons secondBody .nil => by
            have sameBody := (List.cons.inj sameArguments).1
            simpa [Operator.ofSameTerms, erase] using
              congrArg (Pattern.multiLambda count []) sameBody.symm
  | subst =>
      exact match first, second with
        | .cons firstBody (.cons firstReplacement .nil),
            .cons secondBody (.cons secondReplacement .nil) => by
            have sameBody := (List.cons.inj sameArguments).1
            have sameReplacement := (List.cons.inj (List.cons.inj sameArguments).2).1
            simpa [Operator.ofSameTerms, erase] using
              congrArg₂ Pattern.subst sameBody.symm sameReplacement.symm
  | collection =>
      exact congrArg (fun arguments => Pattern.collection _ arguments none)
        sameArguments.symm

private theorem index_liftVarMap_id
    {Γ Δ : List TypeExpr}
    (positions : VarMap id Γ Δ)
    (compatible : ∀ sort (position : Var Γ sort),
      variableIndex (positions sort position) = variableIndex position) :
    ∀ (binders : List TypeExpr) sort
      (position : Var (binders ++ Γ) sort),
      variableIndex (liftVarMap id positions binders sort position) =
        variableIndex position
  | [], _, position => compatible _ position
  | _ :: binders, _, .zero => rfl
  | _ :: binders, _, .succ position =>
      congrArg (· + 1) (index_liftVarMap_id positions compatible binders _ position)

mutual
  private theorem erase_mapTermSame
      {source target : LanguageDef}
      (same : source.terms = target.terms) :
      ∀ {Γ Δ : List TypeExpr}
        (positions : VarMap id Γ Δ)
        (_ : ∀ sort (position : Var Γ sort),
          variableIndex (positions sort position) = variableIndex position)
        {sort : TypeExpr}
        (term : Term (signatureOf source) Γ sort),
        erase (mapTerm (signatureSameTerms same) positions term) = erase term
    | _, _, positions, compatible, _, .var position => by
        change Pattern.bvar (variableIndex (positions _ position)) =
          Pattern.bvar (variableIndex position)
        rw [compatible]
    | _, _, positions, compatible, _, .op operator arguments => by
        change erase (Term.op (Operator.ofSameTerms same operator)
          (castArgsArity ((signatureSameTerms same).carriesArity operator).symm
            (mapArgs (signatureSameTerms same) positions arguments))) =
          erase (Term.op operator arguments)
        apply erase_op_ofSameTerms same operator arguments
        exact (erase_mapArgsSame same positions compatible arguments).symm.trans
          ((eraseArguments_cast
            ((signatureSameTerms same).carriesArity operator).symm
            (mapArgs (signatureSameTerms same) positions arguments)).symm)

  private theorem erase_mapArgsSame
      {source target : LanguageDef}
      (same : source.terms = target.terms) :
      ∀ {Γ Δ : List TypeExpr}
        (positions : VarMap id Γ Δ)
        (_ : ∀ sort (position : Var Γ sort),
          variableIndex (positions sort position) = variableIndex position)
        {arity : List (List TypeExpr × TypeExpr)}
        (arguments : Args (signatureOf source) arity Γ),
        eraseArguments (mapArgs (signatureSameTerms same) positions arguments) =
          eraseArguments arguments
    | _, _, _, _, _, .nil => rfl
    | _, _, positions, compatible, _, .cons (bs := binders) head tail => by
        change erase (mapTerm (signatureSameTerms same)
          (liftVarMap id positions binders) head) ::
            eraseArguments (mapArgs (signatureSameTerms same) positions tail) =
          erase head :: eraseArguments tail
        rw [erase_mapTermSame same _
          (index_liftVarMap_id positions compatible binders) head,
          erase_mapArgsSame same positions compatible tail]
end

/-- A presentation change with the same authored constructors preserves the
existing raw erasure exactly, even inside generic binder representation forms.
This is a syntax theorem, not preservation of rewrites or equations. -/
theorem erase_transportSameTerms {source target : LanguageDef}
    (same : source.terms = target.terms)
    {Γ : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf source) Γ sort) :
    erase (transportSameTerms same term) = erase term := by
  exact erase_mapTermSame same (fun _ position => position)
    (by intro sort position; rfl) term

theorem signatureSameTerms_sort {source target : LanguageDef}
    (same : source.terms = target.terms) (sort : TypeExpr) :
    (signatureSameTerms same).sortMap sort = sort := rfl

#print axioms signatureSameTerms
#print axioms signatureSameTerms_comp_ident
#print axioms transportSameTerms_bind
#print axioms transportSameTerms_symm
#print axioms erase_transportSameTerms
#print axioms Operator.ofSameTerms_symm
#print axioms signatureSameTerms_sort

end Mettapedia.GSLT.LanguageDef.BindingSyntax
