import Mettapedia.GSLT.LanguageDef.BindingSignature
import Mettapedia.OSLF.Syntax.SignatureMorphism
import Mettapedia.OSLF.Syntax.SyntacticTermPresheaf
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Frames

/-!
# The syntax of a language as Transform frames

A declaration supplies sorted constructors and binding arities. The frame
objects are ordinary typed contexts and a frame arrow instantiates their
variables with typed terms. No rules are needed for this action.

Two language definitions with the same grammar (in particular a language
and its syntax-only part) have equivalent substitution categories. The
term presheaves are naturally isomorphic along that equivalence. This
compares the independently derived binding signatures, including
constructor membership and the arities below binders.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.SyntaxOnFrames

open _root_.CategoryTheory
open scoped _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef TypeExpr)
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.BindingSyntax (signatureOf Operator)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface (Frames)

/-- Erase directed rules and authored equations. The grammar declarations,
including binding and collection declarations, are retained. -/
def syntaxPart (language : LanguageDef) : LanguageDef :=
  { language with equations := [], rewrites := [] }

/-- Terms are intrinsically sorted in the source grammar and context. -/
abbrev Terms (language : LanguageDef) (Γ : List TypeExpr) :=
  Σ sort, Term (signatureOf language) Γ sort

/-- Ordinary typed substitution is a Transform frame action. Its equality
is the intrinsic syntax equality of the chosen binding representation. -/
def frames (language : LanguageDef) :
    Frames (Terms language) (Sub (signatureOf language)) where
  E s t := s = t
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act σ t := ⟨t.1, bind σ t.2⟩
  id _ := fun _ x => .var x
  comp τ σ := fun _ x => bind τ (σ _ x)
  act_id t := congrArg (Sigma.mk t.1) (bind_id t.2)
  act_comp τ σ t := congrArg (Sigma.mk t.1) (bind_comp σ τ t.2).symm
  preserves := by
    intro _ _ _ _ _ same
    cases same
    rfl

variable {left middle right : LanguageDef}

/-- Transport a constructor occurrence to a language with the same grammar. -/
private def copyOperator (same : left.terms = right.terms) :
    {sort : TypeExpr} → Operator left sort → Operator right sort
  | _, .constructor rule member ordinary parameters =>
      .constructor rule (same ▸ member) ordinary parameters
  | _, .collectionConstructor rule member name kind sort shape count =>
      .collectionConstructor rule (same ▸ member) name kind sort shape count
  | _, .lambda domain codomain => .lambda domain codomain
  | _, .multiLambda domain codomain n => .multiLambda domain codomain n
  | _, .subst domain codomain => .subst domain codomain
  | _, .collection kind sort n => .collection kind sort n

/-- The arity of a constructor or structural operator is independent of the
operational declarations surrounding it. -/
@[reducible]
def grammarMap (same : left.terms = right.terms) : SigMor (signatureOf left) (signatureOf right) where
  sortMap := fun s => s
  opMap := copyOperator same
  carriesArity op := by
    rw [mapArities_id]
    cases op <;> rfl

private theorem grammarMap_refl (language : LanguageDef) :
    grammarMap (left := language) (right := language) rfl = SigMor.ident _ := by
  unfold grammarMap SigMor.ident
  congr
  funext sort op
  cases op <;> rfl

private theorem grammarMap_comp (one : left.terms = middle.terms) (two : middle.terms = right.terms) :
    (grammarMap one).comp (grammarMap two) = grammarMap (one.trans two) := by
  unfold grammarMap SigMor.comp
  congr 1
  funext sort op
  cases op <;> rfl

def termMap (same : left.terms = right.terms) {Γ : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf left) Γ sort) : Term (signatureOf right) Γ sort :=
  mapTerm (grammarMap same) (fun _ x => x) term

theorem termMap_refl (language : LanguageDef) {Γ : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf language) Γ sort) :
    termMap (left := language) (right := language) rfl term = term := by
  unfold termMap
  exact (eq_of_heq (mapTerm_heq_of_morphism_eq _ _ (grammarMap_refl language)
    (fun _ x => x) (fun _ x => x) HEq.rfl term)).trans
    ((mapTerm_ident (fun _ x => x) term).trans (rename_id term))

theorem termMap_comp (one : left.terms = middle.terms) (two : middle.terms = right.terms)
    {Γ : List TypeExpr} {sort : TypeExpr} (term : Term (signatureOf left) Γ sort) :
    termMap two (termMap one term) = termMap (one.trans two) term := by
  unfold termMap
  rw [mapTerm_comp]
  exact eq_of_heq (mapTerm_heq_of_morphism_eq _ _ (grammarMap_comp one two)
    (fun _ x => x) (fun _ x => x) HEq.rfl term)

def termEquiv (same : left.terms = right.terms) (Γ : List TypeExpr) (sort : TypeExpr) :
    Term (signatureOf left) Γ sort ≃ Term (signatureOf right) Γ sort where
  toFun := termMap same
  invFun := termMap same.symm
  left_inv term := (termMap_comp same same.symm term).trans (termMap_refl left term)
  right_inv term := (termMap_comp same.symm same term).trans (termMap_refl right term)

def substitutionMap (same : left.terms = right.terms) {Γ Δ : List TypeExpr}
    (σ : Sub (signatureOf left) Γ Δ) : Sub (signatureOf right) Γ Δ :=
  fun sort v => termMap same (σ sort v)

/-- The frame square commutes under every typed substitution, including
substitution underneath authored binders. -/
theorem termMap_bind (same : left.terms = right.terms) {Γ Δ : List TypeExpr}
    (σ : Sub (signatureOf left) Γ Δ) {sort : TypeExpr} (term : Term (signatureOf left) Γ sort) :
    termMap same (bind σ term) = bind (substitutionMap same σ) (termMap same term) :=
  mapTerm_bind (grammarMap same) (fun _ v => v) (fun _ v => v) σ _ (fun _ _ => rfl) term

/-- Change a judged term's grammar evidence, preserving its sort. -/
def frameTermEquiv (same : left.terms = right.terms) (Γ : List TypeExpr) :
    Terms left Γ ≃ Terms right Γ :=
  Equiv.sigmaCongrRight (termEquiv same Γ)

theorem frameTermEquiv_act (same : left.terms = right.terms) {Γ Δ : List TypeExpr}
    (σ : Sub (signatureOf left) Γ Δ) (term : Terms left Γ) :
    frameTermEquiv same Δ ((frames left).act σ term) =
      (frames right).act (substitutionMap same σ) (frameTermEquiv same Γ term) := by
  rcases term with ⟨sort, term⟩
  exact congrArg (Sigma.mk sort) (termMap_bind same σ term)

def storeMap (same : left.terms = right.terms) {Γ : List TypeExpr}
    (store : List (Terms left Γ × Terms left Γ)) :
    List (Terms right Γ × Terms right Γ) :=
  store.map (Prod.map (frameTermEquiv same Γ) (frameTermEquiv same Γ))

theorem models_iff (same : left.terms = right.terms) {Γ Δ : List TypeExpr}
    (σ : Sub (signatureOf left) Γ Δ) (store : List (Terms left Γ × Terms left Γ)) :
    (frames right).Models (substitutionMap same σ) (storeMap same store) ↔
      (frames left).Models σ store := by
  constructor
  · intro solved equation member
    have target := solved (Prod.map (frameTermEquiv same Γ) (frameTermEquiv same Γ) equation)
      (List.mem_map_of_mem member)
    change (frames right).act (substitutionMap same σ) (frameTermEquiv same Γ equation.1) =
      (frames right).act (substitutionMap same σ) (frameTermEquiv same Γ equation.2) at target
    rw [← frameTermEquiv_act, ← frameTermEquiv_act] at target
    exact (frameTermEquiv same Δ).injective target
  · intro solved equation member
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    change (frames right).act (substitutionMap same σ) (frameTermEquiv same Γ original.1) =
      (frames right).act (substitutionMap same σ) (frameTermEquiv same Γ original.2)
    rw [← frameTermEquiv_act, ← frameTermEquiv_act]
    exact congrArg (frameTermEquiv same Δ) (solved original inside)

/-- The same restriction on future contexts yields the same solutions on
either side of the syntax comparison. -/
theorem solvable_in_iff (same : left.terms = right.terms) {Γ : List TypeExpr}
    (allowed : List TypeExpr → Prop) (store : List (Terms left Γ × Terms left Γ)) :
    (∃ Δ, allowed Δ ∧ ∃ σ : Sub (signatureOf left) Γ Δ, (frames left).Models σ store) ↔
    (∃ Δ, allowed Δ ∧ ∃ σ : Sub (signatureOf right) Γ Δ, (frames right).Models σ (storeMap same store)) := by
  constructor
  · rintro ⟨Δ, admissible, σ, solved⟩
    exact ⟨Δ, admissible, substitutionMap same σ, (models_iff same σ store).mpr solved⟩
  · rintro ⟨Δ, admissible, σ, solved⟩
    have returned : substitutionMap same (substitutionMap same.symm σ) = σ := by
      funext sort v
      exact (termEquiv same Δ sort).right_inv (σ sort v)
    refine ⟨Δ, admissible, substitutionMap same.symm σ, (models_iff same _ _).mp ?_⟩
    rwa [returned]


/-- Ordinary context maps transport without changing their sorts. -/
def contextFunctor (same : left.terms = right.terms) :
    Syntactic.Ctxt (signatureOf left) ⥤ Syntactic.Ctxt (signatureOf right) where
  obj Γ := ⟨Γ.vars⟩
  map σ := substitutionMap same σ
  map_id _ := rfl
  map_comp first second := by
    funext sort v
    exact termMap_bind same first (second sort v)

/-- Natural comparison of the terms in every frame, along the context map. -/
def termPresheafIso (same : left.terms = right.terms) (sort : TypeExpr) :
    Syntactic.termPresheaf (signatureOf left) sort ≅
      (contextFunctor same).op ⋙ Syntactic.termPresheaf (signatureOf right) sort :=
  NatIso.ofComponents
    (fun Γ => (termEquiv same Γ.unop.vars sort).toIso)
    (by
      intro Γ Δ σ
      apply ConcreteCategory.hom_ext
      intro term
      exact termMap_bind same σ.unop term)

/-- Adding or removing rules gives an equivalence on the underlying
substitution categories. The comparison acts identically on each context. -/
def contextsEquivalence (same : left.terms = right.terms) :
    Syntactic.Ctxt (signatureOf left) ≌ Syntactic.Ctxt (signatureOf right) where
  functor := contextFunctor same
  inverse := contextFunctor same.symm
  unitIso := NatIso.ofComponents (fun Γ => Iso.refl Γ) (by
    intro Γ Δ σ
    funext sort v
    change σ sort v = bind (fun _ x => .var x) (termMap same.symm (termMap same (σ sort v)))
    rw [bind_id]
    exact (termEquiv same Γ.vars sort).left_inv (σ sort v) |>.symm)
  counitIso := NatIso.ofComponents (fun Γ => Iso.refl Γ) (by
    intro Γ Δ σ
    funext sort v
    change termMap same (termMap same.symm (σ sort v)) = bind (fun _ x => .var x) (σ sort v)
    rw [bind_id]
    exact (termEquiv same Γ.vars sort).right_inv (σ sort v))
  functor_unitIso_comp Γ := by
    change (contextFunctor same).map (𝟙 Γ) ≫ 𝟙 (contextFunctor same |>.obj Γ) = _
    simp

/-- On the syntax-only language and on its operational extension, the same
sort has canonically isomorphic term presheaves on the same contexts. -/
def syntaxPartIso (language : LanguageDef) (sort : TypeExpr) :
    Syntactic.termPresheaf (signatureOf (syntaxPart language)) sort ≅
      (contextFunctor (left := syntaxPart language) (right := language) rfl).op ⋙
        Syntactic.termPresheaf (signatureOf language) sort :=
  termPresheafIso (left := syntaxPart language) (right := language) rfl sort

#print axioms termMap_bind
#print axioms solvable_in_iff
#print axioms contextsEquivalence
#print axioms syntaxPartIso

end Mettapedia.GSLT.Compilation.SyntaxOnFrames
