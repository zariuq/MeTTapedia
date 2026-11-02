import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Erasure
import Mettapedia.Logic.HOL.PredicateProducts
import Mettapedia.Logic.HOL.CheckableFragment

/-!
# Annotated predicate readings over a closed lexical interpretation

Closed constant and head codes share the existing HOL weakening operation.
The reader computes carriers from retained binder annotations, checks
application carriers and derives exact coherence from its completeness.
Renaming and represented simultaneous substitution preserve readings.

This is a syntax-directed fragment interpretation, not a model of every type
former or universe. Head-equality and level-instantiation compatibility require
separate proofs for each lexical interpretation. Background assumptions remain
explicit closed formulas; no root theorem or extensionality policy is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- Structural operation keys retain every carrier determined by the input
syntax. Projection keys retain only the pair carrier: a profile with several
layouts on that carrier must select one explicitly or leave the entry absent.
Source typing and semantic laws for the selected operations are separate. -/
inductive StructuralOperator (Base : Type u) where
  | sigma (domain codomain : HOL.Ty Base)
  | identity (endpoint : HOL.Ty Base)
  | pair (first second : HOL.Ty Base)
  | first (pair : HOL.Ty Base)
  | second (pair : HOL.Ty Base)
  | reflexivity (endpoint : HOL.Ty Base)

def StructuralOperator.codeType : StructuralOperator Base → HOL.Ty Base → HOL.Ty Base
  | .sigma domain codomain, result =>
      .arr (.arr domain .prop) (.arr (.arr domain (.arr codomain .prop)) (.arr result .prop))
  | .identity endpoint, result =>
      .arr (.arr endpoint .prop) (.arr endpoint (.arr endpoint (.arr result .prop)))
  | .pair firstType secondType, result => .arr firstType (.arr secondType result)
  | .first pairType, result | .second pairType, result => .arr pairType result
  | .reflexivity endpoint, result => .arr endpoint result

structure LexicalReading (Head : Type) (Base : Type u) (Const : HOL.Ty Base → Type v) where
  constCode? : DeclName → Option (Σ type : HOL.Ty Base, HOL.ClosedTerm Const type)
  headCode? : Head → Option (Σ type : HOL.Ty Base, HOL.ClosedTerm Const type)
  /-- Closed codes make structural interpretation natural in the surrounding
  context. The default preserves the original six-form fragment. Identity
  codes receive the domain guard as well as both endpoints. -/
  structuralCode? : (operator : StructuralOperator Base) →
    Option (Σ result : HOL.Ty Base, HOL.ClosedTerm Const (operator.codeType result)) := fun _ => none

inductive Reads (lex : LexicalReading Head Base Const) :
    {Γ : HOL.Ctx Base} → {type : HOL.Ty Base} →
      CTm Head Γ.length → HOL.Term Const Γ type → Prop where
  | var {Γ : HOL.Ctx Base} {type : HOL.Ty Base} (index : HOL.Var Γ type) :
      Reads lex (.var index.toFin) (.var index)
  | constant {Γ : HOL.Ctx Base} {name : DeclName} {type : HOL.Ty Base}
      {closed : HOL.ClosedTerm Const type} (lookup : lex.constCode? name = some ⟨type, closed⟩) :
      Reads lex (.const name) (HOL.weakenCtx Γ closed)
  | head {Γ : HOL.Ctx Base} {head : Head} {type : HOL.Ty Base}
      {closed : HOL.ClosedTerm Const type} (lookup : lex.headCode? head = some ⟨type, closed⟩) :
      Reads lex (.head head) (HOL.weakenCtx Γ closed)
  | application {Γ : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
      {function argument : CTm Head Γ.length}
      {functionCode : HOL.Term Const Γ (.arr domain codomain)}
      {argumentCode : HOL.Term Const Γ domain} :
      Reads lex function functionCode → Reads lex argument argumentCode →
      Reads lex (.app function argument) (.app functionCode argumentCode)
  | abstraction {Γ : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
      {sourceDomain : CTm Head Γ.length} {body : CTm Head (domain :: Γ).length}
      {domainCode : HOL.Term Const Γ (.arr domain .prop)}
      {code : HOL.Term Const (domain :: Γ) codomain} :
      Reads lex sourceDomain domainCode → Reads lex body code →
      Reads lex (.lam sourceDomain body) (.lam code)
  | product {Γ : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
      {sourceDomain : CTm Head Γ.length} {sourceFamily : CTm Head (domain :: Γ).length}
      {domainCode : HOL.Term Const Γ (.arr domain .prop)}
      {familyCode : HOL.Term Const (domain :: Γ) (.arr codomain .prop)} :
      Reads lex sourceDomain domainCode → Reads lex sourceFamily familyCode →
      Reads lex (.pi sourceDomain sourceFamily) (HOL.PredicateProducts.pi domainCode familyCode)
  | dependentSum {Γ : HOL.Ctx Base} {domain codomain result : HOL.Ty Base}
      {sourceDomain : CTm Head Γ.length} {sourceFamily : CTm Head (domain :: Γ).length}
      {domainCode : HOL.Term Const Γ (.arr domain .prop)}
      {familyCode : HOL.Term Const (domain :: Γ) (.arr codomain .prop)}
      {closed : HOL.ClosedTerm Const ((StructuralOperator.sigma domain codomain).codeType result)}
      (lookup : lex.structuralCode? (.sigma domain codomain) = some ⟨result, closed⟩) :
      Reads lex sourceDomain domainCode → Reads lex sourceFamily familyCode →
      Reads lex (.sigma sourceDomain sourceFamily)
        (.app (.app (HOL.weakenCtx Γ closed) domainCode) (.lam familyCode))
  | identity {Γ : HOL.Ctx Base} {endpoint result : HOL.Ty Base}
      {sourceDomain left right : CTm Head Γ.length}
      {domainCode : HOL.Term Const Γ (.arr endpoint .prop)}
      {leftCode rightCode : HOL.Term Const Γ endpoint}
      {closed : HOL.ClosedTerm Const ((StructuralOperator.identity endpoint).codeType result)}
      (lookup : lex.structuralCode? (.identity endpoint) = some ⟨result, closed⟩) :
      Reads lex sourceDomain domainCode → Reads lex left leftCode → Reads lex right rightCode →
      Reads lex (.id sourceDomain left right)
        (.app (.app (.app (HOL.weakenCtx Γ closed) domainCode) leftCode) rightCode)
  | pair {Γ : HOL.Ctx Base} {first second result : HOL.Ty Base}
      {left right : CTm Head Γ.length} {leftCode : HOL.Term Const Γ first}
      {rightCode : HOL.Term Const Γ second}
      {closed : HOL.ClosedTerm Const ((StructuralOperator.pair first second).codeType result)}
      (lookup : lex.structuralCode? (.pair first second) = some ⟨result, closed⟩) :
      Reads lex left leftCode → Reads lex right rightCode →
      Reads lex (.pair left right) (.app (.app (HOL.weakenCtx Γ closed) leftCode) rightCode)
  | first {Γ : HOL.Ctx Base} {pair result : HOL.Ty Base}
      {source : CTm Head Γ.length} {code : HOL.Term Const Γ pair}
      {closed : HOL.ClosedTerm Const ((StructuralOperator.first pair).codeType result)}
      (lookup : lex.structuralCode? (.first pair) = some ⟨result, closed⟩) :
      Reads lex source code → Reads lex (.fst source) (.app (HOL.weakenCtx Γ closed) code)
  | second {Γ : HOL.Ctx Base} {pair result : HOL.Ty Base}
      {source : CTm Head Γ.length} {code : HOL.Term Const Γ pair}
      {closed : HOL.ClosedTerm Const ((StructuralOperator.second pair).codeType result)}
      (lookup : lex.structuralCode? (.second pair) = some ⟨result, closed⟩) :
      Reads lex source code → Reads lex (.snd source) (.app (HOL.weakenCtx Γ closed) code)
  | reflexivity {Γ : HOL.Ctx Base} {endpoint result : HOL.Ty Base}
      {source : CTm Head Γ.length} {code : HOL.Term Const Γ endpoint}
      {closed : HOL.ClosedTerm Const ((StructuralOperator.reflexivity endpoint).codeType result)}
      (lookup : lex.structuralCode? (.reflexivity endpoint) = some ⟨result, closed⟩) :
      Reads lex source code → Reads lex (.refl source) (.app (HOL.weakenCtx Γ closed) code)

namespace Reads

theorem rename {lex : LexicalReading Head Base Const}
    {Γ Ξ : HOL.Ctx Base} {type : HOL.Ty Base}
    {source : CTm Head Γ.length} {code : HOL.Term Const Γ type}
    (reading : Reads lex source code)
    (ρ : HOL.Rename Base Γ Ξ) (raw : Ren Γ.length Ξ.length)
    (compatible : ∀ {type} (index : HOL.Var Γ type),
      (ρ index).toFin = raw (index.toFin)) :
    Reads lex (source.rename raw) (HOL.rename ρ code) := by
  induction reading generalizing Ξ with
  | var index => simpa only [CTm.rename, HOL.rename, compatible] using Reads.var (ρ index)
  | constant lookup => simpa only [CTm.rename, HOL.rename_weakenCtx] using (Reads.constant (Γ := Ξ) lookup)
  | head lookup => simpa only [CTm.rename, HOL.rename_weakenCtx] using (Reads.head (Γ := Ξ) lookup)
  | application _ _ first second => exact .application (first ρ raw compatible) (second ρ raw compatible)
  | abstraction _ _ domain body =>
      apply Reads.abstraction (domain ρ raw compatible)
      apply body (HOL.Rename.lift ρ) (liftRen raw)
      intro type index
      cases index with
      | vz => rfl
      | vs prior => exact congrArg Fin.succ (compatible prior)
  | product _ _ domain family =>
      rw [HOL.PredicateProducts.rename_pi]
      apply Reads.product (domain ρ raw compatible)
      apply family (HOL.Rename.lift ρ) (liftRen raw)
      intro type index
      cases index with
      | vz => rfl
      | vs prior => exact congrArg Fin.succ (compatible prior)
  | dependentSum lookup _ _ domain family =>
      simp only [HOL.rename, HOL.rename_weakenCtx]
      apply Reads.dependentSum lookup (domain ρ raw compatible)
      apply family (HOL.Rename.lift ρ) (liftRen raw)
      intro type index
      cases index with
      | vz => rfl
      | vs prior => exact congrArg Fin.succ (compatible prior)
  | identity lookup _ _ _ domain left right =>
      simpa only [CTm.rename, HOL.rename, HOL.rename_weakenCtx] using
        Reads.identity lookup (domain ρ raw compatible) (left ρ raw compatible) (right ρ raw compatible)
  | pair lookup _ _ left right =>
      simpa only [CTm.rename, HOL.rename, HOL.rename_weakenCtx] using
        Reads.pair lookup (left ρ raw compatible) (right ρ raw compatible)
  | first lookup _ argument =>
      simpa only [CTm.rename, HOL.rename, HOL.rename_weakenCtx] using Reads.first lookup (argument ρ raw compatible)
  | second lookup _ argument =>
      simpa only [CTm.rename, HOL.rename, HOL.rename_weakenCtx] using Reads.second lookup (argument ρ raw compatible)
  | reflexivity lookup _ argument =>
      simpa only [CTm.rename, HOL.rename, HOL.rename_weakenCtx] using Reads.reflexivity lookup (argument ρ raw compatible)

theorem substitute {lex : LexicalReading Head Base Const}
    {Γ Ξ : HOL.Ctx Base} {type : HOL.Ty Base}
    {source : CTm Head Γ.length} {code : HOL.Term Const Γ type}
    (reading : Reads lex source code)
    (θ : HOL.Subst Const Γ Ξ) (raw : CSub Head Γ.length Ξ.length)
    (components : ∀ {type} (index : HOL.Var Γ type),
      Reads lex (raw (index.toFin)) (θ index)) :
    Reads lex (source.subst raw) (HOL.subst θ code) := by
  induction reading generalizing Ξ with
  | var index => exact components index
  | constant lookup => simpa only [CTm.subst, HOL.subst_weakenCtx] using (Reads.constant (Γ := Ξ) lookup)
  | head lookup => simpa only [CTm.subst, HOL.subst_weakenCtx] using (Reads.head (Γ := Ξ) lookup)
  | application _ _ first second => exact .application (first θ raw components) (second θ raw components)
  | abstraction _ _ domain body =>
      apply Reads.abstraction (domain θ raw components)
      apply body (HOL.Subst.lift θ) (CTm.liftSub raw)
      intro type index
      cases index with
      | vz => exact .var .vz
      | vs prior => exact (components prior).rename HOL.Rename.weaken wk (fun _ => rfl)
  | product _ _ domain family =>
      rw [HOL.PredicateProducts.subst_pi]
      apply Reads.product (domain θ raw components)
      apply family (HOL.Subst.lift θ) (CTm.liftSub raw)
      intro type index
      cases index with
      | vz => exact .var .vz
      | vs prior => exact (components prior).rename HOL.Rename.weaken wk (fun _ => rfl)
  | dependentSum lookup _ _ domain family =>
      simp only [HOL.subst, HOL.subst_weakenCtx]
      apply Reads.dependentSum lookup (domain θ raw components)
      apply family (HOL.Subst.lift θ) (CTm.liftSub raw)
      intro type index
      cases index with
      | vz => exact .var .vz
      | vs prior => exact (components prior).rename HOL.Rename.weaken wk (fun _ => rfl)
  | identity lookup _ _ _ domain left right =>
      simpa only [CTm.subst, HOL.subst, HOL.subst_weakenCtx] using
        Reads.identity lookup (domain θ raw components) (left θ raw components) (right θ raw components)
  | pair lookup _ _ left right =>
      simpa only [CTm.subst, HOL.subst, HOL.subst_weakenCtx] using
        Reads.pair lookup (left θ raw components) (right θ raw components)
  | first lookup _ argument =>
      simpa only [CTm.subst, HOL.subst, HOL.subst_weakenCtx] using Reads.first lookup (argument θ raw components)
  | second lookup _ argument =>
      simpa only [CTm.subst, HOL.subst, HOL.subst_weakenCtx] using Reads.second lookup (argument θ raw components)
  | reflexivity lookup _ argument =>
      simpa only [CTm.subst, HOL.subst, HOL.subst_weakenCtx] using Reads.reflexivity lookup (argument θ raw components)

/-- A change of source heads with exact lexical-code agreement. This does not
supply a morphism of source typing rules or a change of HOL carriers. -/
structure HeadChange {Head' : Type} (source : LexicalReading Head Base Const)
    (target : LexicalReading Head' Base Const) (map : Head → Head') : Prop where
  constants : ∀ name, target.constCode? name = source.constCode? name
  heads : ∀ head, target.headCode? (map head) = source.headCode? head
  structural : ∀ operator, target.structuralCode? operator = source.structuralCode? operator := by intros; rfl

theorem changeHeads {Head' : Type} {sourceLex : LexicalReading Head Base Const}
    {targetLex : LexicalReading Head' Base Const} {map : Head → Head'}
    (compatible : HeadChange sourceLex targetLex map)
    {Γ : HOL.Ctx Base} {type : HOL.Ty Base} {source : CTm Head Γ.length} {code : HOL.Term Const Γ type}
    (reading : Reads sourceLex source code) : Reads targetLex (source.mapHead map) code := by
  induction reading with
  | var index => exact .var index
  | constant lookup => exact .constant ((compatible.constants _).trans lookup)
  | head lookup => exact .head ((compatible.heads _).trans lookup)
  | application _ _ function argument => exact .application function argument
  | abstraction _ _ domain body => exact .abstraction domain body
  | product _ _ domain family => exact .product domain family
  | dependentSum lookup _ _ domain family =>
      exact .dependentSum ((compatible.structural _).trans lookup) domain family
  | identity lookup _ _ _ domain left right =>
      exact .identity ((compatible.structural _).trans lookup) domain left right
  | pair lookup _ _ left right => exact .pair ((compatible.structural _).trans lookup) left right
  | first lookup _ argument => exact .first ((compatible.structural _).trans lookup) argument
  | second lookup _ argument => exact .second ((compatible.structural _).trans lookup) argument
  | reflexivity lookup _ argument => exact .reflexivity ((compatible.structural _).trans lookup) argument

/-- Exact lookup agreement also reflects readings of mapped source terms. -/
theorem ofChangeHeads {Head' : Type} {sourceLex : LexicalReading Head Base Const}
    {targetLex : LexicalReading Head' Base Const} {map : Head → Head'}
    (compatible : HeadChange sourceLex targetLex map) :
    {Γ : HOL.Ctx Base} → {type : HOL.Ty Base} → (source : CTm Head Γ.length) →
    {code : HOL.Term Const Γ type} → Reads targetLex (source.mapHead map) code → Reads sourceLex source code
  | _, _, .var position, _, reading => by
      change Reads targetLex (.var position) _ at reading
      cases reading
      exact .var _
  | _, _, .const name, _, reading => by
      change Reads targetLex (.const name) _ at reading
      cases reading with
      | constant lookup => exact .constant ((compatible.constants _).symm.trans lookup)
  | _, _, .head sourceHead, _, reading => by
      change Reads targetLex (.head (map sourceHead)) _ at reading
      cases reading with
      | head lookup => exact .head ((compatible.heads _).symm.trans lookup)
  | _, _, .app function argument, _, reading => by
      change Reads targetLex (.app (function.mapHead map) (argument.mapHead map)) _ at reading
      cases reading with
      | application first second =>
          exact .application (ofChangeHeads compatible function first) (ofChangeHeads compatible argument second)
  | Γ, _, .lam domain body, _, reading => by
      change Reads targetLex (.lam (domain.mapHead map) (body.mapHead map)) _ at reading
      cases reading with
      | abstraction first second =>
          exact .abstraction (ofChangeHeads compatible domain first) (ofChangeHeads compatible (Γ := _ :: Γ) body second)
  | Γ, _, .pi domain family, _, reading => by
      change Reads targetLex (.pi (domain.mapHead map) (family.mapHead map)) _ at reading
      cases reading with
      | product first second =>
          exact .product (ofChangeHeads compatible domain first) (ofChangeHeads compatible (Γ := _ :: Γ) family second)
  | Γ, _, .sigma domain family, _, reading => by
      change Reads targetLex (.sigma (domain.mapHead map) (family.mapHead map)) _ at reading
      cases reading with
      | dependentSum lookup first second =>
          exact .dependentSum ((compatible.structural _).symm.trans lookup)
            (ofChangeHeads compatible domain first) (ofChangeHeads compatible (Γ := _ :: Γ) family second)
  | _, _, .id domain left right, _, reading => by
      change Reads targetLex (.id (domain.mapHead map) (left.mapHead map) (right.mapHead map)) _ at reading
      cases reading with
      | identity lookup domainRead leftRead rightRead =>
          exact .identity ((compatible.structural _).symm.trans lookup)
            (ofChangeHeads compatible domain domainRead) (ofChangeHeads compatible left leftRead)
            (ofChangeHeads compatible right rightRead)
  | _, _, .pair left right, _, reading => by
      change Reads targetLex (.pair (left.mapHead map) (right.mapHead map)) _ at reading
      cases reading with
      | pair lookup first second =>
          exact .pair ((compatible.structural _).symm.trans lookup)
            (ofChangeHeads compatible left first) (ofChangeHeads compatible right second)
  | _, _, .fst source, _, reading => by
      change Reads targetLex (.fst (source.mapHead map)) _ at reading
      cases reading with
      | first lookup argument =>
          exact .first ((compatible.structural _).symm.trans lookup) (ofChangeHeads compatible source argument)
  | _, _, .snd source, _, reading => by
      change Reads targetLex (.snd (source.mapHead map)) _ at reading
      cases reading with
      | second lookup argument =>
          exact .second ((compatible.structural _).symm.trans lookup) (ofChangeHeads compatible source argument)
  | _, _, .refl source, _, reading => by
      change Reads targetLex (.refl (source.mapHead map)) _ at reading
      cases reading with
      | reflexivity lookup argument =>
          exact .reflexivity ((compatible.structural _).symm.trans lookup) (ofChangeHeads compatible source argument)

theorem HeadChange.carrier_eq_of_collision {Head' : Type}
    {source : LexicalReading Head Base Const} {target : LexicalReading Head' Base Const} {map : Head → Head'}
    (compatible : HeadChange source target map) {first second : Head}
    (collision : map first = map second) {firstType secondType : HOL.Ty Base}
    {firstCode : HOL.ClosedTerm Const firstType} {secondCode : HOL.ClosedTerm Const secondType}
    (firstRead : source.headCode? first = some ⟨firstType, firstCode⟩)
    (secondRead : source.headCode? second = some ⟨secondType, secondCode⟩) : firstType = secondType := by
  have firstTarget := (compatible.heads first).trans firstRead
  have secondTarget : target.headCode? (map first) = some ⟨secondType, secondCode⟩ := by
    rw [collision]
    exact (compatible.heads second).trans secondRead
  exact congrArg Sigma.fst (Option.some.inj (firstTarget.symm.trans secondTarget))

end Reads

namespace Reader

abbrev Result (lex : LexicalReading Head Base Const) (Γ : HOL.Ctx Base)
    (source : CTm Head Γ.length) :=
  {value : (Σ type : HOL.Ty Base, HOL.Term Const Γ type) //
    Reads lex source value.2}

variable [DecidableEq Base]

/-- Syntax-directed reading with a constructed derivation at every branch. -/
def read? (lex : LexicalReading Head Base Const) : (Γ : HOL.Ctx Base) →
    (source : CTm Head Γ.length) → Option (Result lex Γ source)
  | Γ, .var index =>
      some ⟨⟨Γ.get index, .var (HOL.Var.ofFin Γ index)⟩, by
        simpa only [HOL.CheckableFragment.Var.toFin_ofFin] using
          (Reads.var (lex := lex) (HOL.Var.ofFin Γ index))⟩
  | Γ, .const name =>
      match lookup : lex.constCode? name with
      | some ⟨type, closed⟩ => some ⟨⟨type, HOL.weakenCtx Γ closed⟩, .constant lookup⟩
      | none => none
  | Γ, .head head =>
      match lookup : lex.headCode? head with
      | some ⟨type, closed⟩ => some ⟨⟨type, HOL.weakenCtx Γ closed⟩, .head lookup⟩
      | none => none
  | Γ, .app function argument =>
      match read? lex Γ function with
      | some ⟨⟨.arr domain codomain, functionCode⟩, functionRead⟩ =>
          match read? lex Γ argument with
          | some ⟨⟨argumentType, argumentCode⟩, argumentRead⟩ =>
              if same : argumentType = domain then
                some ⟨⟨codomain, .app functionCode (same ▸ argumentCode)⟩,
                  .application functionRead (by cases same; exact argumentRead)⟩
              else none
          | none => none
      | _ => none
  | Γ, .lam domain body =>
      match read? lex Γ domain with
      | some ⟨⟨.arr carrier .prop, domainCode⟩, domainRead⟩ =>
          match read? lex (carrier :: Γ) body with
          | some ⟨⟨bodyType, bodyCode⟩, bodyRead⟩ =>
              some ⟨⟨.arr carrier bodyType, .lam bodyCode⟩, .abstraction domainRead bodyRead⟩
          | none => none
      | _ => none
  | Γ, .pi domain family =>
      match read? lex Γ domain with
      | some ⟨⟨.arr carrier .prop, domainCode⟩, domainRead⟩ =>
          match read? lex (carrier :: Γ) family with
          | some ⟨⟨.arr codomain .prop, familyCode⟩, familyRead⟩ =>
              some ⟨⟨.arr (.arr carrier codomain) .prop, HOL.PredicateProducts.pi domainCode familyCode⟩,
                .product domainRead familyRead⟩
          | _ => none
      | _ => none
  | Γ, .sigma domain family =>
      match read? lex Γ domain with
      | some ⟨⟨.arr carrier .prop, domainCode⟩, domainRead⟩ =>
          match read? lex (carrier :: Γ) family with
          | some ⟨⟨.arr codomain .prop, familyCode⟩, familyRead⟩ =>
              match lookup : lex.structuralCode? (.sigma carrier codomain) with
              | some ⟨result, closed⟩ =>
                  some ⟨⟨.arr result .prop, .app (.app (HOL.weakenCtx Γ closed) domainCode) (.lam familyCode)⟩,
                    .dependentSum lookup domainRead familyRead⟩
              | none => none
          | _ => none
      | _ => none
  | Γ, .id domain left right =>
      match read? lex Γ domain with
      | some ⟨⟨.arr endpoint .prop, domainCode⟩, domainRead⟩ =>
          match read? lex Γ left, read? lex Γ right with
          | some ⟨⟨leftType, leftCode⟩, leftRead⟩, some ⟨⟨rightType, rightCode⟩, rightRead⟩ =>
              if first : leftType = endpoint then
                if second : rightType = endpoint then
                  match lookup : lex.structuralCode? (.identity endpoint) with
                  | some ⟨result, closed⟩ =>
                      some ⟨⟨.arr result .prop, .app (.app (.app (HOL.weakenCtx Γ closed)
                        domainCode) (first ▸ leftCode)) (second ▸ rightCode)⟩,
                        .identity lookup domainRead (by cases first; exact leftRead)
                          (by cases second; exact rightRead)⟩
                  | none => none
                else none
              else none
          | _, _ => none
      | _ => none
  | Γ, .pair left right =>
      match read? lex Γ left, read? lex Γ right with
      | some ⟨⟨first, leftCode⟩, leftRead⟩, some ⟨⟨second, rightCode⟩, rightRead⟩ =>
          match lookup : lex.structuralCode? (.pair first second) with
          | some ⟨result, closed⟩ =>
              some ⟨⟨result, .app (.app (HOL.weakenCtx Γ closed) leftCode) rightCode⟩,
                .pair lookup leftRead rightRead⟩
          | none => none
      | _, _ => none
  | Γ, .fst source =>
      match read? lex Γ source with
      | some ⟨⟨pair, code⟩, reading⟩ =>
          match lookup : lex.structuralCode? (.first pair) with
          | some ⟨result, closed⟩ =>
              some ⟨⟨result, .app (HOL.weakenCtx Γ closed) code⟩, .first lookup reading⟩
          | none => none
      | none => none
  | Γ, .snd source =>
      match read? lex Γ source with
      | some ⟨⟨pair, code⟩, reading⟩ =>
          match lookup : lex.structuralCode? (.second pair) with
          | some ⟨result, closed⟩ =>
              some ⟨⟨result, .app (HOL.weakenCtx Γ closed) code⟩, .second lookup reading⟩
          | none => none
      | none => none
  | Γ, .refl source =>
      match read? lex Γ source with
      | some ⟨⟨endpoint, code⟩, reading⟩ =>
          match lookup : lex.structuralCode? (.reflexivity endpoint) with
          | some ⟨result, closed⟩ =>
              some ⟨⟨result, .app (HOL.weakenCtx Γ closed) code⟩, .reflexivity lookup reading⟩
          | none => none
      | none => none

/-- Every derivation in the independently defined fragment is recovered,
including its exact carrier and term. Proof irrelevance only identifies the
stored evidence fields; it does not identify different terms. -/
theorem read?_complete {lex : LexicalReading Head Base Const} {Γ : HOL.Ctx Base}
    {type : HOL.Ty Base} {source : CTm Head Γ.length} {code : HOL.Term Const Γ type}
    (reading : Reads lex source code) :
    read? lex Γ source = some ⟨⟨type, code⟩, reading⟩ := by
  induction reading with
  | var index =>
      simp only [read?]
      apply congrArg some
      apply Subtype.ext
      dsimp only
      have recovered := HOL.CheckableFragment.elaborate?_erase (Const := Const) (HOL.Term.var index)
      simp only [HOL.CheckableFragment.erase, HOL.CheckableFragment.elaborate?] at recovered
      exact Option.some.inj recovered
  | constant lookup =>
      simp only [read?]
      split
      · rename_i type closed found
        cases Option.some.inj (found.symm.trans lookup)
        rfl
      · rename_i found
        cases found.symm.trans lookup
  | head lookup =>
      simp only [read?]
      split
      · rename_i type closed found
        cases Option.some.inj (found.symm.trans lookup)
        rfl
      · rename_i found
        cases found.symm.trans lookup
  | application first second ihFirst ihSecond => simp [read?, ihFirst, ihSecond]
  | abstraction domain body ihDomain ihBody => simp [read?, ihDomain, ihBody]
  | product domain family ihDomain ihFamily => simp [read?, ihDomain, ihFamily]
  | dependentSum lookup domain family ihDomain ihFamily =>
      simp only [read?, ihDomain, ihFamily]
      split
      · rename_i result closed found
        cases Option.some.inj (found.symm.trans lookup)
        rfl
      · rename_i found
        cases found.symm.trans lookup
  | identity lookup domain left right ihDomain ihLeft ihRight =>
      simp only [read?, ihDomain, ihLeft, ihRight, ↓reduceDIte]
      split
      · rename_i result closed found
        cases Option.some.inj (found.symm.trans lookup)
        rfl
      · rename_i found
        cases found.symm.trans lookup
  | pair lookup left right ihLeft ihRight =>
      simp only [read?, ihLeft, ihRight]
      split
      · rename_i result closed found
        cases Option.some.inj (found.symm.trans lookup)
        rfl
      · rename_i found
        cases found.symm.trans lookup
  | first lookup argument ih =>
      simp only [read?, ih]
      split
      · rename_i result closed found
        cases Option.some.inj (found.symm.trans lookup)
        rfl
      · rename_i found
        cases found.symm.trans lookup
  | second lookup argument ih =>
      simp only [read?, ih]
      split
      · rename_i result closed found
        cases Option.some.inj (found.symm.trans lookup)
        rfl
      · rename_i found
        cases found.symm.trans lookup
  | reflexivity lookup argument ih =>
      simp only [read?, ih]
      split
      · rename_i result closed found
        cases Option.some.inj (found.symm.trans lookup)
        rfl
      · rename_i found
        cases found.symm.trans lookup

/-- The executable result omits the proof field, retaining its inferred
carrier and exact HOL term. -/
def infer? (lex : LexicalReading Head Base Const) (Γ : HOL.Ctx Base)
    (source : CTm Head Γ.length) : Option (Σ type : HOL.Ty Base, HOL.Term Const Γ type) :=
  (read? lex Γ source).map Subtype.val

theorem infer?_sound (lex : LexicalReading Head Base Const) (Γ : HOL.Ctx Base)
    (source : CTm Head Γ.length) (type : HOL.Ty Base) (code : HOL.Term Const Γ type)
    (accepted : infer? lex Γ source = some ⟨type, code⟩) :
    Reads lex source code := by
  obtain ⟨reading, _, same⟩ := Option.map_eq_some_iff.mp accepted
  exact Eq.mp (congrArg (fun value : (Σ type : HOL.Ty Base, HOL.Term Const Γ type) =>
    Reads lex source value.2) same) reading.2

theorem infer?_complete {lex : LexicalReading Head Base Const} {Γ : HOL.Ctx Base}
    {type : HOL.Ty Base} {source : CTm Head Γ.length} {code : HOL.Term Const Γ type}
    (reading : Reads lex source code) :
    infer? lex Γ source = some ⟨type, code⟩ := by
  simp only [infer?, read?_complete reading, Option.map_some]

theorem infer?_iff (lex : LexicalReading Head Base Const) (Γ : HOL.Ctx Base)
    (source : CTm Head Γ.length) (type : HOL.Ty Base) (code : HOL.Term Const Γ type) :
    infer? lex Γ source = some ⟨type, code⟩ ↔ Reads lex source code :=
  ⟨infer?_sound lex Γ source type code, infer?_complete⟩

/-- The annotations determine both the simple carrier and the exact target
syntax. No equality of readings is added as an assumption. -/
theorem coherent {lex : LexicalReading Head Base Const} {Γ : HOL.Ctx Base}
    {firstType secondType : HOL.Ty Base} {source : CTm Head Γ.length}
    {first : HOL.Term Const Γ firstType} {second : HOL.Term Const Γ secondType}
    (firstRead : Reads lex source first)
    (secondRead : Reads lex source second) :
    (⟨firstType, first⟩ : Σ type : HOL.Ty Base, HOL.Term Const Γ type) = ⟨secondType, second⟩ :=
  Option.some.inj ((infer?_complete firstRead).symm.trans (infer?_complete secondRead))

theorem term_unique {lex : LexicalReading Head Base Const} {Γ : HOL.Ctx Base}
    {type : HOL.Ty Base} {source : CTm Head Γ.length}
    {first second : HOL.Term Const Γ type}
    (firstRead : Reads lex source first)
    (secondRead : Reads lex source second) : first = second := by
  exact eq_of_heq (Sigma.mk.inj_iff.mp (coherent firstRead secondRead)).2

theorem infer?_substitute {lex : LexicalReading Head Base Const} {Γ Ξ : HOL.Ctx Base}
    {type : HOL.Ty Base} {source : CTm Head Γ.length} {code : HOL.Term Const Γ type}
    (accepted : infer? lex Γ source = some ⟨type, code⟩)
    (θ : HOL.Subst Const Γ Ξ) (raw : CSub Head Γ.length Ξ.length)
    (components : ∀ {type} (index : HOL.Var Γ type),
      infer? lex Ξ (raw (index.toFin)) = some ⟨type, θ index⟩) :
    infer? lex Ξ (source.subst raw) = some ⟨type, HOL.subst θ code⟩ :=
  infer?_complete ((infer?_sound _ _ _ _ _ accepted).substitute θ raw
    (fun index => infer?_sound _ _ _ _ _ (components index)))

theorem infer?_rename {lex : LexicalReading Head Base Const} {Γ Ξ : HOL.Ctx Base}
    {type : HOL.Ty Base} {source : CTm Head Γ.length} {code : HOL.Term Const Γ type}
    (accepted : infer? lex Γ source = some ⟨type, code⟩)
    (ρ : HOL.Rename Base Γ Ξ) (raw : Ren Γ.length Ξ.length)
    (compatible : ∀ {type} (index : HOL.Var Γ type),
      (ρ index).toFin = raw (index.toFin)) :
    infer? lex Ξ (source.rename raw) = some ⟨type, HOL.rename ρ code⟩ :=
  infer?_complete ((infer?_sound _ _ _ _ _ accepted).rename ρ raw compatible)

abbrev Assignment (lex : LexicalReading Head Base Const) (source target : HOL.Ctx Base)
    (raw : CSub Head source.length target.length) :=
  {assignment : HOL.Subst Const source target // ∀ {type} (index : HOL.Var source type),
    Reads lex (Γ := target) (raw index.toFin) (assignment index)}

/-- Read every component at its declared carrier, retaining the entire
simultaneous assignment and its pointwise interpretation. -/
def readAssignment? (lex : LexicalReading Head Base Const) : (source target : HOL.Ctx Base) →
    (raw : CSub Head source.length target.length) → Option (Assignment lex source target raw)
  | [], _, _ => some ⟨(fun index => nomatch index), (fun index => nomatch index)⟩
  | domain :: source, target, raw =>
      match read? lex target (raw (HOL.Var.vz (Γ := source) (τ := domain)).toFin) with
      | none => none
      | some ⟨⟨type, code⟩, reading⟩ =>
          if same : type = domain then
            match readAssignment? lex source target (fun index => raw index.succ) with
            | none => none
            | some tail => some ⟨(fun index => match index with
                | .vz => same ▸ code
                | .vs prior => tail.val prior), by
                  intro type index
                  cases index with
                  | vz => cases same; exact reading
                  | vs prior => exact tail.property prior⟩
          else none

theorem readAssignment?_complete (lex : LexicalReading Head Base Const) (source target : HOL.Ctx Base) :
    ∀ (raw : CSub Head source.length target.length) (assignment : HOL.Subst Const source target)
      (represented : ∀ {type} (index : HOL.Var source type),
        Reads lex (Γ := target) (raw index.toFin) (assignment index)),
      readAssignment? lex source target raw = some ⟨assignment, represented⟩ := by
  induction source with
  | nil =>
      intro raw assignment represented
      simp only [readAssignment?]
      apply congrArg some
      apply Subtype.ext
      funext type index
      cases index
  | cons domain source ih =>
      intro raw assignment represented
      have head := read?_complete (represented (HOL.Var.vz (Γ := source) (τ := domain)))
      have tail := ih (fun index => raw index.succ) (fun index => assignment (.vs index))
        (fun index => represented (.vs index))
      simp only [readAssignment?, head, dite_true, tail]
      apply congrArg some
      apply Subtype.ext
      funext type index
      cases index <;> rfl

theorem infer?_changeHeads {Head' : Type} {sourceLex : LexicalReading Head Base Const}
    {targetLex : LexicalReading Head' Base Const} {map : Head → Head'}
    (compatible : Reads.HeadChange sourceLex targetLex map)
    {Γ : HOL.Ctx Base} {type : HOL.Ty Base} {source : CTm Head Γ.length} {code : HOL.Term Const Γ type}
    (accepted : infer? sourceLex Γ source = some ⟨type, code⟩) :
    infer? targetLex Γ (source.mapHead map) = some ⟨type, code⟩ :=
  infer?_complete ((infer?_sound _ _ _ _ _ accepted).changeHeads compatible)

theorem infer?_changeHeads_iff {Head' : Type} {sourceLex : LexicalReading Head Base Const}
    {targetLex : LexicalReading Head' Base Const} {map : Head → Head'}
    (compatible : Reads.HeadChange sourceLex targetLex map)
    (Γ : HOL.Ctx Base) (source : CTm Head Γ.length) (type : HOL.Ty Base) (code : HOL.Term Const Γ type) :
    infer? targetLex Γ (source.mapHead map) = some ⟨type, code⟩ ↔
      infer? sourceLex Γ source = some ⟨type, code⟩ :=
  ⟨fun accepted => infer?_complete (Reads.ofChangeHeads compatible source
      (infer?_sound _ _ _ _ _ accepted)), infer?_changeHeads compatible⟩

end Reader

def assumptions (closed : List (HOL.ClosedFormula Const)) (Γ : HOL.Ctx Base) :
    List (HOL.Formula Const Γ) := closed.map (HOL.weakenCtx Γ)

theorem assumptions_substitute (closed : List (HOL.ClosedFormula Const))
    {Γ Ξ : HOL.Ctx Base} (theta : HOL.Subst Const Γ Ξ) :
    (assumptions closed Γ).map (HOL.subst theta) = assumptions closed Ξ := by
  simp only [assumptions, List.map_map]
  apply List.map_congr_left
  intro formula _
  exact HOL.subst_weakenCtx theta formula

theorem assumptions_weaken (closed : List (HOL.ClosedFormula Const))
    (Γ : HOL.Ctx Base) (domain : HOL.Ty Base) :
    HOL.weakenHyps (σ := domain) (assumptions closed Γ) = assumptions closed (domain :: Γ) := by
  simp only [assumptions, HOL.weakenHyps, List.map_map]
  apply List.map_congr_left
  intro formula _
  exact (HOL.weakenCtx_cons formula).symm

namespace Controls
/-- A lexical control with two distinct carriers and no nonlogical constants.
Only reading and head transport are asserted, not source typing or a universe model. -/
abbrev Symbols (_type : HOL.Ty Unit) := Empty
abbrev carrier : HOL.Ty Unit := .base ()
def original : LexicalReading Nat Unit Symbols where
  constCode? := fun _ => none
  headCode? := fun head =>
    if head = 0 then some ⟨.arr carrier .prop, HOL.PredicateProducts.full carrier⟩
    else if head = 1 then some ⟨.arr (.arr carrier carrier) .prop, HOL.PredicateProducts.full (.arr carrier carrier)⟩
    else none

def shifted : LexicalReading Nat Unit Symbols where
  constCode? := original.constCode?
  headCode? := fun head => if head = 0 then none else original.headCode? (head - 1)

theorem shift_compatible : Reads.HeadChange original shifted Nat.succ where
  constants := fun _ => rfl
  heads := fun head => by simp [shifted]

def identity : CTm Nat 0 := .lam (.head 0) (.var 0)
def identityCode : HOL.ClosedTerm Symbols (.arr carrier carrier) := .lam (.var .vz)

theorem identity_read : Reader.infer? original [] identity = some ⟨.arr carrier carrier, identityCode⟩ := by
  apply Reader.infer?_complete
  apply Reads.abstraction (domainCode := HOL.PredicateProducts.full carrier) (.head rfl)
  have indexSame : (HOL.Var.vz : HOL.Var [carrier] carrier).toFin = (0 : Fin [carrier].length) := by
    apply Fin.ext
    rfl
  rw [← indexSame]
  exact Reads.var (lex := original) (Γ := [carrier]) HOL.Var.vz

theorem shifted_identity_read :
    Reader.infer? shifted [] (identity.mapHead Nat.succ) = some ⟨.arr carrier carrier, identityCode⟩ :=
  Reader.infer?_changeHeads shift_compatible identity_read

theorem reflected_identity_read :
    Reader.infer? shifted [] (identity.mapHead Nat.succ) = some ⟨.arr carrier carrier, identityCode⟩ ↔
      Reader.infer? original [] identity = some ⟨.arr carrier carrier, identityCode⟩ :=
  Reader.infer?_changeHeads_iff shift_compatible [] identity _ identityCode

theorem collapsed_heads_refused (target : LexicalReading Nat Unit Symbols) :
    ¬ Reads.HeadChange original target (fun _ => 0) := by
  intro compatible
  have impossible := compatible.carrier_eq_of_collision (first := 0) (second := 1) rfl
    (firstCode := (HOL.PredicateProducts.full carrier : HOL.ClosedTerm Symbols _))
    (secondCode := (HOL.PredicateProducts.full (.arr carrier carrier) : HOL.ClosedTerm Symbols _)) rfl rfl
  cases impossible
end Controls

#print axioms Reader.readAssignment?_complete
#print axioms Reads.ofChangeHeads
#print axioms Reader.infer?_changeHeads_iff
#print axioms Reads.changeHeads
#print axioms Reads.HeadChange.carrier_eq_of_collision
#print axioms Controls.shifted_identity_read
#print axioms Controls.collapsed_heads_refused

#print axioms Reads.rename
#print axioms Reads.substitute
#print axioms Reader.read?
#print axioms Reader.read?_complete
#print axioms Reader.coherent
#print axioms assumptions_substitute
#print axioms assumptions_weaken
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
