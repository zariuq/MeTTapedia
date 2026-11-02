import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalPredicateReading
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Erasure
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Elaboration

/-!
# The natural predicate reading with retained lambda domains

This reading uses the original Church-style syntax. A lambda's actual domain
must itself read as a predicate on its selected simple carrier. The domain
therefore fixes the HOL binder type instead of allowing an unconstrained
erasure choice. Forgetting the annotations recovers the existing predicate
reading; renaming and simultaneous substitution preserve the stronger reading.

The admitted constructors are natural declarations, the selected motive
universe, products, variables, application and annotated abstraction. Other
dependent formers require their own interpretation and are not admitted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open FormationSensitiveHOLInterface (variableIndex)

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- The Nat fragment supplies closed lexical entries to the shared reader. -/
def lexicalReading (operations : Operations Base Const) :
    AnnotatedPredicateReading.LexicalReading Tower.Head Base Const where
  constCode? := fun name =>
    if name = natName then some ⟨.arr operations.number .prop, HOL.PredicateProducts.full operations.number⟩
    else if name = zeroName then some ⟨operations.number, operations.zero⟩
    else if name = succName then some ⟨.arr operations.number operations.number, operations.successor⟩
    else if name = natEliminateName then some ⟨operations.eliminatorType, operations.eliminator⟩
    else none
  headCode? := fun head =>
    if head = .sort motiveLevel then
      some ⟨.arr (.arr operations.result .prop) .prop, HOL.PredicateProducts.full (.arr operations.result .prop)⟩
    else none

theorem variableIndex_eq_toFin {Γ : HOL.Ctx Base} {type : HOL.Ty Base} (index : HOL.Var Γ type) :
    variableIndex index = index.toFin := by
  induction index with
  | vz => rfl
  | vs prior ih => exact congrArg Fin.succ ih

theorem variableIndex_ofFin (Γ : HOL.Ctx Base) (index : Fin Γ.length) :
    variableIndex (HOL.Var.ofFin Γ index) = index := by
  rw [variableIndex_eq_toFin]
  exact HOL.CheckableFragment.Var.toFin_ofFin Γ index

theorem weaken_full (Γ : HOL.Ctx Base) (type : HOL.Ty Base) :
    HOL.weakenCtx Γ (HOL.PredicateProducts.full type : HOL.ClosedTerm Const _) =
      HOL.PredicateProducts.full type := by
  induction Γ with
  | nil => rfl
  | cons domain Γ ih =>
      rw [HOL.weakenCtx_cons, ih]
      exact HOL.PredicateProducts.rename_full HOL.Rename.weaken type

theorem Operations.weaken_eliminator (operations : Operations Base Const) (Γ : HOL.Ctx Base) :
    HOL.weakenCtx Γ (operations.eliminator (Γ := [])) = operations.eliminator (Γ := Γ) := by
  induction Γ with
  | nil => rfl
  | cons domain Γ ih =>
      rw [HOL.weakenCtx_cons, ih]
      exact operations.rename_eliminator HOL.Rename.weaken

inductive AnnotatedReads (operations : Operations Base Const) :
    {Γ : HOL.Ctx Base} → {type : HOL.Ty Base} →
      CTm Tower.Head Γ.length → HOL.Term Const Γ type → Prop where
  | var {Γ : HOL.Ctx Base} {type : HOL.Ty Base} (index : HOL.Var Γ type) :
      AnnotatedReads operations (.var (variableIndex index)) (.var index)
  | natural {Γ : HOL.Ctx Base} :
      AnnotatedReads operations (.const natName : CTm Tower.Head Γ.length)
        (HOL.PredicateProducts.full operations.number)
  | zero {Γ : HOL.Ctx Base} :
      AnnotatedReads operations (.const zeroName : CTm Tower.Head Γ.length)
        (HOL.weakenCtx Γ operations.zero)
  | successor {Γ : HOL.Ctx Base} :
      AnnotatedReads operations (.const succName : CTm Tower.Head Γ.length)
        (HOL.weakenCtx Γ operations.successor)
  | motiveUniverse {Γ : HOL.Ctx Base} :
      AnnotatedReads operations (.head (.sort motiveLevel) : CTm Tower.Head Γ.length)
        (HOL.PredicateProducts.full (.arr operations.result .prop))
  | eliminator {Γ : HOL.Ctx Base} :
      AnnotatedReads operations (.const natEliminateName : CTm Tower.Head Γ.length)
        operations.eliminator
  | application {Γ : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
      {function argument : CTm Tower.Head Γ.length}
      {functionCode : HOL.Term Const Γ (.arr domain codomain)}
      {argumentCode : HOL.Term Const Γ domain} :
      AnnotatedReads operations function functionCode → AnnotatedReads operations argument argumentCode →
      AnnotatedReads operations (.app function argument) (.app functionCode argumentCode)
  | abstraction {Γ : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
      {sourceDomain : CTm Tower.Head Γ.length} {body : CTm Tower.Head (domain :: Γ).length}
      {domainCode : HOL.Term Const Γ (.arr domain .prop)}
      {code : HOL.Term Const (domain :: Γ) codomain} :
      AnnotatedReads operations sourceDomain domainCode → AnnotatedReads operations body code →
      AnnotatedReads operations (.lam sourceDomain body) (.lam code)
  | product {Γ : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
      {sourceDomain : CTm Tower.Head Γ.length} {sourceFamily : CTm Tower.Head (domain :: Γ).length}
      {domainCode : HOL.Term Const Γ (.arr domain .prop)}
      {familyCode : HOL.Term Const (domain :: Γ) (.arr codomain .prop)} :
      AnnotatedReads operations sourceDomain domainCode → AnnotatedReads operations sourceFamily familyCode →
      AnnotatedReads operations (.pi sourceDomain sourceFamily) (HOL.PredicateProducts.pi domainCode familyCode)

namespace AnnotatedReads

/-- The maintained annotation of a lambda-free source introduces no unknown
domains. In particular, this applies to the original natural computation
schemas before their caller substitutions are installed. -/
theorem of_lamFree {operations : Operations Base Const}
    {Γ : HOL.Ctx Base} {type : HOL.Ty Base} {source : Tower.Tm Γ.length}
    {code : HOL.Term Const Γ type} (reading : Reads operations source code)
    (noLambda : lamFree source = true) : AnnotatedReads operations (liftTm source) code := by
  induction reading with
  | var index => exact .var index
  | natural => exact .natural
  | zero => exact .zero
  | successor => exact .successor
  | motiveUniverse => exact .motiveUniverse
  | eliminator => exact .eliminator
  | application _ _ first second =>
      simp only [lamFree, Bool.and_eq_true] at noLambda
      exact .application (first noLambda.1) (second noLambda.2)
  | abstraction _ _ => contradiction
  | product _ _ domain family =>
      simp only [lamFree, Bool.and_eq_true] at noLambda
      exact .product (domain noLambda.1) (family noLambda.2)

theorem erase {operations : Operations Base Const}
    {Γ : HOL.Ctx Base} {type : HOL.Ty Base} {source : CTm Tower.Head Γ.length}
    {code : HOL.Term Const Γ type} (reading : AnnotatedReads operations source code) :
    Reads operations source.erase code := by
  induction reading with
  | var index => exact .var index
  | natural => exact .natural
  | zero => exact .zero
  | successor => exact .successor
  | motiveUniverse => exact .motiveUniverse
  | eliminator => exact .eliminator
  | application _ _ first second => exact .application first second
  | abstraction _ _ _ body => exact .abstraction body
  | product _ _ first second => exact .product first second

theorem rename {operations : Operations Base Const}
    {Γ Ξ : HOL.Ctx Base} {type : HOL.Ty Base}
    {source : CTm Tower.Head Γ.length} {code : HOL.Term Const Γ type}
    (reading : AnnotatedReads operations source code)
    (ρ : HOL.Rename Base Γ Ξ) (raw : Ren Γ.length Ξ.length)
    (compatible : ∀ {type} (index : HOL.Var Γ type),
      variableIndex (ρ index) = raw (variableIndex index)) :
    AnnotatedReads operations (source.rename raw) (HOL.rename ρ code) := by
  induction reading generalizing Ξ with
  | var index => simpa only [CTm.rename, HOL.rename, compatible] using AnnotatedReads.var (ρ index)
  | natural => simpa only [CTm.rename, HOL.PredicateProducts.rename_full] using (AnnotatedReads.natural (Γ := Ξ))
  | zero => simpa only [CTm.rename, HOL.rename_weakenCtx] using (AnnotatedReads.zero (Γ := Ξ))
  | successor => simpa only [CTm.rename, HOL.rename_weakenCtx] using (AnnotatedReads.successor (Γ := Ξ))
  | motiveUniverse => exact .motiveUniverse
  | eliminator => simpa only [CTm.rename, Operations.rename_eliminator] using (AnnotatedReads.eliminator (Γ := Ξ))
  | application _ _ first second => exact .application (first ρ raw compatible) (second ρ raw compatible)
  | abstraction _ _ domain body =>
      apply AnnotatedReads.abstraction (domain ρ raw compatible)
      apply body (HOL.Rename.lift ρ) (liftRen raw)
      intro type index
      cases index with
      | vz => rfl
      | vs prior => exact congrArg Fin.succ (compatible prior)
  | product _ _ domain family =>
      rw [HOL.PredicateProducts.rename_pi]
      apply AnnotatedReads.product (domain ρ raw compatible)
      apply family (HOL.Rename.lift ρ) (liftRen raw)
      intro type index
      cases index with
      | vz => rfl
      | vs prior => exact congrArg Fin.succ (compatible prior)

theorem substitute {operations : Operations Base Const}
    {Γ Ξ : HOL.Ctx Base} {type : HOL.Ty Base}
    {source : CTm Tower.Head Γ.length} {code : HOL.Term Const Γ type}
    (reading : AnnotatedReads operations source code)
    (θ : HOL.Subst Const Γ Ξ) (raw : CSub Tower.Head Γ.length Ξ.length)
    (components : ∀ {type} (index : HOL.Var Γ type),
      AnnotatedReads operations (raw (variableIndex index)) (θ index)) :
    AnnotatedReads operations (source.subst raw) (HOL.subst θ code) := by
  induction reading generalizing Ξ with
  | var index => exact components index
  | natural => simpa only [CTm.subst, HOL.PredicateProducts.subst_full] using (AnnotatedReads.natural (Γ := Ξ))
  | zero => simpa only [CTm.subst, HOL.subst_weakenCtx] using (AnnotatedReads.zero (Γ := Ξ))
  | successor => simpa only [CTm.subst, HOL.subst_weakenCtx] using (AnnotatedReads.successor (Γ := Ξ))
  | motiveUniverse => exact .motiveUniverse
  | eliminator => simpa only [CTm.subst, Operations.subst_eliminator] using (AnnotatedReads.eliminator (Γ := Ξ))
  | application _ _ first second => exact .application (first θ raw components) (second θ raw components)
  | abstraction _ _ domain body =>
      apply AnnotatedReads.abstraction (domain θ raw components)
      apply body (HOL.Subst.lift θ) (CTm.liftSub raw)
      intro type index
      cases index with
      | vz => exact .var .vz
      | vs prior => exact (components prior).rename HOL.Rename.weaken wk (fun _ => rfl)
  | product _ _ domain family =>
      rw [HOL.PredicateProducts.subst_pi]
      apply AnnotatedReads.product (domain θ raw components)
      apply family (HOL.Subst.lift θ) (CTm.liftSub raw)
      intro type index
      cases index with
      | vz => exact .var .vz
      | vs prior => exact (components prior).rename HOL.Rename.weaken wk (fun _ => rfl)

/-- The original Nat reading embeds in the shared lexical interpretation. -/
theorem toGeneric {operations : Operations Base Const} {Γ : HOL.Ctx Base} {type : HOL.Ty Base}
    {source : CTm Tower.Head Γ.length} {code : HOL.Term Const Γ type}
    (reading : AnnotatedReads operations source code) :
    AnnotatedPredicateReading.Reads (lexicalReading operations) source code := by
  induction reading with
  | var index =>
      simpa only [variableIndex_eq_toFin] using
        (AnnotatedPredicateReading.Reads.var (lex := lexicalReading operations) index)
  | natural =>
      simpa only [weaken_full] using
        (AnnotatedPredicateReading.Reads.constant (lex := lexicalReading operations) (name := natName)
          (closed := HOL.PredicateProducts.full operations.number)
          (by simp [lexicalReading]))
  | zero => exact .constant (by simp [lexicalReading, natName, zeroName])
  | successor => exact .constant (by simp [lexicalReading, natName, zeroName, succName])
  | motiveUniverse =>
      simpa only [weaken_full] using
        (AnnotatedPredicateReading.Reads.head (lex := lexicalReading operations) (head := .sort motiveLevel)
          (closed := HOL.PredicateProducts.full (.arr operations.result .prop))
          (by simp [lexicalReading]))
  | eliminator =>
      simpa only [Operations.weaken_eliminator] using
        (AnnotatedPredicateReading.Reads.constant (lex := lexicalReading operations) (name := natEliminateName)
          (closed := operations.eliminator (Γ := []))
          (by simp [lexicalReading, natName, zeroName, succName, natEliminateName]))
  | application _ _ first second => exact .application first second
  | abstraction _ _ domain body => exact .abstraction domain body
  | product _ _ domain family => exact .product domain family

/-- The shared implementation admits exactly the independently specified Nat
fragment, including the precise target carrier and term. -/
theorem ofGeneric {operations : Operations Base Const} {Γ : HOL.Ctx Base} {type : HOL.Ty Base}
    {source : CTm Tower.Head Γ.length} {code : HOL.Term Const Γ type}
    (reading : AnnotatedPredicateReading.Reads (lexicalReading operations) source code) :
    AnnotatedReads operations source code := by
  induction reading with
  | var index => simpa only [variableIndex_eq_toFin] using (AnnotatedReads.var (operations := operations) index)
  | constant lookup =>
      simp only [lexicalReading] at lookup
      split at lookup
      · rename_i same
        cases same
        cases Option.some.inj lookup
        simpa only [weaken_full] using (AnnotatedReads.natural (operations := operations))
      · split at lookup
        · rename_i same
          cases same
          cases Option.some.inj lookup
          exact .zero
        · split at lookup
          · rename_i same
            cases same
            cases Option.some.inj lookup
            exact .successor
          · split at lookup
            · rename_i same
              cases same
              cases Option.some.inj lookup
              simpa only [Operations.weaken_eliminator] using (AnnotatedReads.eliminator (operations := operations))
            · cases lookup
  | head lookup =>
      simp only [lexicalReading] at lookup
      split at lookup
      · rename_i same
        cases same
        cases Option.some.inj lookup
        simpa only [weaken_full] using (AnnotatedReads.motiveUniverse (operations := operations))
      · cases lookup
  | application _ _ first second => exact .application first second
  | abstraction _ _ domain body => exact .abstraction domain body
  | product _ _ domain family => exact .product domain family

  | dependentSum lookup _ _ _ _ => cases lookup
  | identity lookup _ _ _ _ _ _ => cases lookup
  | pair lookup _ _ _ _ => cases lookup
  | first lookup _ _ => cases lookup
  | second lookup _ _ => cases lookup
  | reflexivity lookup _ _ => cases lookup

theorem generic_iff {operations : Operations Base Const} {Γ : HOL.Ctx Base} {type : HOL.Ty Base}
    {source : CTm Tower.Head Γ.length} {code : HOL.Term Const Γ type} :
    AnnotatedPredicateReading.Reads (lexicalReading operations) source code ↔ AnnotatedReads operations source code :=
  ⟨ofGeneric, toGeneric⟩

end AnnotatedReads

#print axioms AnnotatedReads.toGeneric
#print axioms AnnotatedReads.ofGeneric
#print axioms AnnotatedReads.erase
#print axioms AnnotatedReads.of_lamFree
#print axioms AnnotatedReads.rename
#print axioms AnnotatedReads.substitute

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
