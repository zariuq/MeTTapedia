import Mettapedia.SetTheory.Profiles.ProfileIndexedCalculus

/-!
# Expansion of derived rules into their actual source deductions

A derived rule carries an earlier proof. Expansion concatenates that
proof's genuine law declarations and substitutes its deduction into the
calling proof. The source law list is not treated as a new set of axioms.
Consequently adding these derived rules is syntactically conservative.
Profile compilations can use this stronger contract when a source law is
derived, rather than primitive, in the target profile.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileIndexedCalculus

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula)
open GraphRealizedDeduction (Proof)

universe u v

theorem declarationFormulas_append {profile : Profile.{u}} {count : Nat}
    (first second : List (Declaration profile count)) :
    declarationFormulas (first ++ second) = declarationFormulas first ++ declarationFormulas second := by
  simp only [declarationFormulas, List.map_append]

/-- Each source occurrence is compiled to its independently retained
proof. An origin labels the rule occurrence at the call site. -/
structure Compilation (source : Profile.{u}) (target : Profile.{v}) where
  rule : {count : Nat} → {body : Formula count} →
    (origin : Nat) → source.Rule body → Derivation target [] body

def Compilation.adoption {source : Profile.{u}} {target : Profile.{v}}
    (compilation : Compilation source target) {count : Nat} {body : Formula count}
    (origin : Nat) : Adoption source body → Derivation target [] body
  | .primitive rule => compilation.rule origin rule
  | .substitution indices previous => by
      simpa only [List.map_nil] using (compilation.adoption origin previous).substitute indices

structure CompiledContext (profile : Profile.{u}) {count : Nat} (formulas : List (Formula count)) where
  declarations : List (Declaration profile count)
  proofs : (index : Fin formulas.length) → Proof (declarationFormulas declarations) formulas[index.val]

def CompiledContext.empty (profile : Profile.{u}) (count : Nat) :
    CompiledContext profile ([] : List (Formula count)) :=
  ⟨[], fun index => Fin.elim0 index⟩

def CompiledContext.cons {profile : Profile.{u}} {count : Nat}
    {formulas : List (Formula count)} {formula : Formula count}
    (head : Derivation profile [] formula) (tail : CompiledContext profile formulas) :
    CompiledContext profile (formula :: formulas) where
  declarations := head.declarations ++ tail.declarations
  proofs := by
    rw [declarationFormulas_append]
    intro index
    refine Fin.cases ?_ (fun earlier => ?_) index
    · change Proof _ formula
      exact appendLeft (declarationFormulas tail.declarations)
        (by simpa only [List.append_nil] using head.proof)
    · change Proof _ formulas[earlier.val]
      exact appendRight (declarationFormulas head.declarations) (tail.proofs earlier)

def Compilation.declarations {source : Profile.{u}} {target : Profile.{v}}
    (compilation : Compilation source target) {count : Nat} :
    (declarations : List (Declaration source count)) →
      CompiledContext target (declarationFormulas declarations)
  | [] => CompiledContext.empty target count
  | head :: tail =>
      CompiledContext.cons (compilation.adoption head.origin head.adoption)
        (compilation.declarations tail)

/-- Every primitive or derived source law is expanded into the target's
actual proof before the caller's complete logical tree is replayed. -/
def Compilation.derivation {source : Profile.{u}} {target : Profile.{v}}
    (compilation : Compilation source target) {count : Nat}
    {assumptions : List (Formula count)} {conclusion : Formula count}
    (derivation : Derivation source assumptions conclusion) :
    Derivation target assumptions conclusion :=
  let compiled := compilation.declarations derivation.declarations
  ⟨compiled.declarations,
    substituteHypotheses derivation.proof (appendReplacements
      (fun index => appendLeft assumptions (compiled.proofs index))
      (fun index => appendRight (declarationFormulas compiled.declarations) (Proof.hypothesis index)))⟩

inductive DerivedRule (profile : Profile.{u}) : {count : Nat} → Formula count → Type u where
  | original {count : Nat} {body : Formula count} (rule : profile.Rule body) : DerivedRule profile body
  | derived {count : Nat} {body : Formula count}
      (name : Nat) (source : Derivation profile [] body) : DerivedRule profile body

def withDerivedRules (profile : Profile.{u}) : Profile.{u} where
  RuleName := profile.RuleName ⊕ Nat
  Rule := DerivedRule profile
  ruleName := fun rule => match rule with
    | .original earlier => .inl (profile.ruleName earlier)
    | .derived name _ => .inr name

def derivedEmbedding (profile : Profile.{u}) : Translation profile (withDerivedRules profile) where
  rule := fun rule => .primitive (.original rule)

def expandDerived (profile : Profile.{u}) : Compilation (withDerivedRules profile) profile where
  rule := fun origin rule => match rule with
    | .original earlier => Derivation.adopt origin (.primitive earlier)
    | .derived _ source => source

/-- The conservativity theorem concerns all formulas and local contexts,
and constructs an actual earlier-profile derivation. -/
def derived_conservative {profile : Profile.{u}} {count : Nat}
    {assumptions : List (Formula count)} {conclusion : Formula count}
    (derivation : Derivation (withDerivedRules profile) assumptions conclusion) :
    Derivation profile assumptions conclusion := (expandDerived profile).derivation derivation

theorem derived_derivable_iff {profile : Profile.{u}} {count : Nat}
    (assumptions : List (Formula count)) (conclusion : Formula count) :
    Nonempty (Derivation (withDerivedRules profile) assumptions conclusion) ↔
      Nonempty (Derivation profile assumptions conclusion) :=
  ⟨fun ⟨proof⟩ => ⟨derived_conservative proof⟩,
    fun ⟨proof⟩ => ⟨(derivedEmbedding profile).derivation proof⟩⟩

/-- The authored premise of a derived rule is retained as its expansion,
not certified by re-declaring the desired conclusion as an axiom. -/
theorem expand_derived_rule {profile : Profile.{u}} {count : Nat} {body : Formula count}
    (name origin : Nat) (source : Derivation profile [] body) :
    (expandDerived profile).rule origin (DerivedRule.derived name source) = source := rfl

end Mettapedia.SetTheory.Profiles.ProfileIndexedCalculus
