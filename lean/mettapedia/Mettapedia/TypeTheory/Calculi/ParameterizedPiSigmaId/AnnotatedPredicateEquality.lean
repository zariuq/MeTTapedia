import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateInstantiation

/-!
# Retained equality proofs over a lexical predicate reading

The endpoints retain the exact annotated source and its computed HOL code.
Composition derives midpoint agreement from the shared reader. Background
hypotheses are closed formulas transported uniformly into each context.
Extensionality freedom is a property of a proof, not a restriction on this
interface: different root theories may carry different explicit dependencies.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
  {lex : LexicalReading Head Base Const} {closed : List (HOL.ClosedFormula Const)} {Γ : HOL.Ctx Base}

structure EqualityAt (lex : LexicalReading Head Base Const) (closed : List (HOL.ClosedFormula Const))
    (Γ : HOL.Ctx Base) (source target : CTm Head Γ.length) (carrier : HOL.Ty Base) where
  left : HOL.Term Const Γ carrier
  right : HOL.Term Const Γ carrier
  leftRead : Reads lex source left
  rightRead : Reads lex target right
  proof : HOL.ProofSyntax Const (assumptions closed Γ) (.eq left right)

abbrev EqualityReading (lex : LexicalReading Head Base Const) (closed : List (HOL.ClosedFormula Const))
    (Γ : HOL.Ctx Base) (source target : CTm Head Γ.length) :=
  (carrier : HOL.Ty Base) × EqualityAt lex closed Γ source target carrier

namespace EqualityAt

def refl {source : CTm Head Γ.length} {carrier : HOL.Ty Base} {term : HOL.Term Const Γ carrier}
    (reading : Reads lex source term) : EqualityAt lex closed Γ source source carrier :=
  ⟨term, term, reading, reading, .eqRefl term⟩

def symm {source target : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (reading : EqualityAt lex closed Γ source target carrier) : EqualityAt lex closed Γ target source carrier :=
  ⟨reading.right, reading.left, reading.rightRead, reading.leftRead, .eqSymm reading.proof⟩

def app {f g a b : CTm Head Γ.length} {domain codomain : HOL.Ty Base}
    (function : EqualityAt lex closed Γ f g (.arr domain codomain))
    (argument : EqualityAt lex closed Γ a b domain) : EqualityAt lex closed Γ (.app f a) (.app g b) codomain :=
  ⟨.app function.left argument.left, .app function.right argument.right,
    .application function.leftRead argument.leftRead, .application function.rightRead argument.rightRead,
    HOL.ProofSyntax.appCongr function.proof argument.proof⟩

def lam {A A' : CTm Head Γ.length} {body body' : CTm Head (Γ.length + 1)} {domain codomain : HOL.Ty Base}
    (domains : EqualityAt lex closed Γ A A' (.arr domain .prop))
    (bodies : EqualityAt lex closed (domain :: Γ) body body' codomain) :
    EqualityAt lex closed Γ (.lam A body) (.lam A' body') (.arr domain codomain) :=
  ⟨.lam bodies.left, .lam bodies.right, .abstraction domains.leftRead bodies.leftRead,
    .abstraction domains.rightRead bodies.rightRead,
    .eqLam (HOL.ProofSyntax.castIndices (assumptions_weaken closed Γ domain).symm rfl bodies.proof)⟩

def pi {A A' : CTm Head Γ.length} {B B' : CTm Head (Γ.length + 1)} {domain codomain : HOL.Ty Base}
    (domains : EqualityAt lex closed Γ A A' (.arr domain .prop))
    (families : EqualityAt lex closed (domain :: Γ) B B' (.arr codomain .prop)) :
    EqualityAt lex closed Γ (.pi A B) (.pi A' B') (.arr (.arr domain codomain) .prop) :=
  ⟨HOL.PredicateProducts.pi domains.left families.left, HOL.PredicateProducts.pi domains.right families.right,
    .product domains.leftRead families.leftRead, .product domains.rightRead families.rightRead,
    HOL.PredicateProducts.congruence domains.proof
      (HOL.ProofSyntax.castIndices (assumptions_weaken closed Γ domain).symm rfl families.proof)⟩

def beta {A : CTm Head Γ.length} {body : CTm Head (Γ.length + 1)} {argument : CTm Head Γ.length}
    {domain codomain : HOL.Ty Base} {domainCode : HOL.Term Const Γ (.arr domain .prop)}
    {bodyCode : HOL.Term Const (domain :: Γ) codomain} {argumentCode : HOL.Term Const Γ domain}
    (domainRead : Reads lex A domainCode) (bodyRead : Reads lex (Γ := domain :: Γ) body bodyCode)
    (argumentRead : Reads lex argument argumentCode) :
    EqualityAt lex closed Γ (.app (.lam A body) argument) (CTm.inst0 argument body) codomain :=
  ⟨.app (.lam bodyCode) argumentCode, HOL.instantiate argumentCode bodyCode,
    .application (.abstraction domainRead bodyRead) argumentRead, bodyRead.instantiate argumentRead,
    .beta argumentCode bodyCode⟩

def substitute {Ξ : HOL.Ctx Base} {source target : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (reading : EqualityAt lex closed Γ source target carrier)
    (raw : CSub Head Γ.length Ξ.length) (assignment : HOL.Subst Const Γ Ξ)
    (represented : ∀ {type} (index : HOL.Var Γ type), Reads lex (raw index.toFin) (assignment index)) :
    EqualityAt lex closed Ξ (source.subst raw) (target.subst raw) carrier :=
  ⟨HOL.subst assignment reading.left, HOL.subst assignment reading.right,
    reading.leftRead.substitute assignment raw represented, reading.rightRead.substitute assignment raw represented,
    HOL.ProofSyntax.castIndices (assumptions_substitute closed assignment) rfl
      (HOL.ProofSyntax.subst assignment reading.proof)⟩

theorem substitute_free {Ξ : HOL.Ctx Base} {source target : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (reading : EqualityAt lex closed Γ source target carrier)
    (raw : CSub Head Γ.length Ξ.length) (assignment : HOL.Subst Const Γ Ξ)
    (represented : ∀ {type} (index : HOL.Var Γ type), Reads lex (raw index.toFin) (assignment index))
    (free : reading.proof.FunctionExtensionalityFree) :
    (reading.substitute raw assignment represented).proof.FunctionExtensionalityFree := by
  simpa only [substitute, HOL.ProofSyntax.functionExtensionalityFree_castIndices,
    HOL.ProofSyntax.functionExtensionalityFree_subst] using free

def castEndpoints {source target source' target' : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (left : source = source') (right : target = target')
    (reading : EqualityAt lex closed Γ source target carrier) : EqualityAt lex closed Γ source' target' carrier :=
  left ▸ right ▸ reading

@[simp] theorem castEndpoints_left {source target source' target' : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (left : source = source') (right : target = target') (reading : EqualityAt lex closed Γ source target carrier) :
    (reading.castEndpoints left right).left = reading.left := by
  cases left
  cases right
  rfl

@[simp] theorem castEndpoints_right {source target source' target' : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (left : source = source') (right : target = target') (reading : EqualityAt lex closed Γ source target carrier) :
    (reading.castEndpoints left right).right = reading.right := by
  cases left
  cases right
  rfl

theorem castEndpoints_proof {source target source' target' : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (left : source = source') (right : target = target') (reading : EqualityAt lex closed Γ source target carrier) :
    HEq (reading.castEndpoints left right).proof reading.proof := by
  cases left
  cases right
  rfl

theorem castEndpoints_free {source target source' target' : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (left : source = source') (right : target = target') (reading : EqualityAt lex closed Γ source target carrier)
    (free : reading.proof.FunctionExtensionalityFree) :
    (reading.castEndpoints left right).proof.FunctionExtensionalityFree := by
  cases left
  cases right
  exact free
end EqualityAt

namespace EqualityReading
variable [DecidableEq Base]

def trans {source middle target : CTm Head Γ.length}
    (first : EqualityReading lex closed Γ source middle) (second : EqualityReading lex closed Γ middle target) :
    EqualityReading lex closed Γ source target := by
  obtain ⟨carrier, first⟩ := first
  obtain ⟨carrier', second⟩ := second
  have same : carrier = carrier' := congrArg Sigma.fst (Reader.coherent first.rightRead second.leftRead)
  cases same
  have midpoint := Reader.term_unique second.leftRead first.rightRead
  exact ⟨carrier, first.left, second.right, first.leftRead, second.rightRead,
    .eqTrans first.proof (HOL.ProofSyntax.castIndices rfl
      (congrArg (fun term => HOL.Term.eq term second.right) midpoint) second.proof)⟩
end EqualityReading

#print axioms EqualityAt.substitute
#print axioms EqualityAt.substitute_free
#print axioms EqualityReading.trans
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
