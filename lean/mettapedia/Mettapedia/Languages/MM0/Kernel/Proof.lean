import Mettapedia.Languages.MM0.Kernel.Conversion
import Mettapedia.Languages.MM0.Kernel.SubstitutionTyping

/-!
# MM0 proof judgments and theorem instances

The theorem signature contains available axioms and previously proved theorems.
Its sequential admission is separate from proof checking. An application fetches
the actual declaration, checks substitution against its formal context, and
derives every substituted hypothesis. Conversion uses the independent typed
conversion judgment. Local hypotheses are assumptions, not theorem declarations.

Logical derivability does not impose an ordering on proofs of the premises.
The list judgment records all premises and is equivalent to pointwise
derivability. Submitted certificates retain their own ordered child evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

structure TheoremDecl where
  arguments : Context
  hypotheses : List Preterm
  conclusion : Preterm

abbrev TheoremSignature := Nat → Option TheoremDecl

namespace Substitution

def substituteList (substitution : Substitution) : List Preterm → Option (List Preterm)
  | [] => some []
  | expression :: expressions => do
      let result ← expression.substitute substitution
      let results ← substituteList substitution expressions
      pure (result :: results)

theorem substituteList_eq_some_iff (substitution : Substitution)
    (sources results : List Preterm) :
    substituteList substitution sources = some results ↔
      List.Forall₂ (Preterm.Substitutes substitution) sources results := by
  induction sources generalizing results with
  | nil => cases results <;> simp [substituteList]
  | cons source sources ih =>
      cases results with
      | nil =>
          cases first : source.substitute substitution <;>
            cases rest : substituteList substitution sources <;>
            simp [substituteList, first, rest]
      | cons result results =>
          cases first : source.substitute substitution <;>
            cases rest : substituteList substitution sources <;>
            simp [substituteList, first, rest, ← Preterm.substitute_eq_some_iff, ← ih]

theorem substituteList_none_iff (substitution : Substitution) (sources : List Preterm) :
    substituteList substitution sources = none ↔
      ¬ ∃ results, List.Forall₂ (Preterm.Substitutes substitution) sources results := by
  constructor
  · intro refused ⟨results, substituted⟩
    have success := (substituteList_eq_some_iff _ _ _).mpr substituted
    rw [refused] at success
    contradiction
  · intro impossible
    cases result : substituteList substitution sources with
    | none => rfl
    | some results =>
        exact False.elim (impossible ⟨results, (substituteList_eq_some_iff _ _ _).mp result⟩)

end Substitution

structure TheoremInstance where
  hypotheses : List Preterm
  conclusion : Preterm
  deriving DecidableEq, Repr

namespace TheoremDecl

/-- Relational simultaneous substitution of this declaration, with dependency safety. -/
structure Instantiates (signature : TermSignature) (target : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) (instantiation : TheoremInstance) : Prop where
  admissible : Substitution.Admissible signature declaration.arguments target arguments
  hypotheses : List.Forall₂ (Preterm.Substitutes (Substitution.ofList arguments))
    declaration.hypotheses instantiation.hypotheses
  conclusion : Preterm.Substitutes (Substitution.ofList arguments)
    declaration.conclusion instantiation.conclusion

def instantiate? (signature : TermSignature) (target : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) : Option TheoremInstance :=
  if Substitution.checkAdmissible signature declaration.arguments target arguments then do
    let hypotheses ← Substitution.substituteList (Substitution.ofList arguments)
      declaration.hypotheses
    let conclusion ← declaration.conclusion.substitute (Substitution.ofList arguments)
    pure ⟨hypotheses, conclusion⟩
  else none

theorem Instantiates.eval {signature : TermSignature} {target : Context}
    {declaration : TheoremDecl} {arguments : List Preterm} {instantiation : TheoremInstance}
    (instantiated : Instantiates signature target declaration arguments instantiation) :
    instantiate? signature target declaration arguments = some instantiation := by
  rcases instantiated with ⟨admitted, hypotheses, conclusion⟩
  rcases instantiation with ⟨instHypotheses, instConclusion⟩
  simp [instantiate?, (Substitution.checkAdmissible_iff _ _ _ _).mpr admitted,
    (Substitution.substituteList_eq_some_iff _ _ _).mpr hypotheses, conclusion.eval]

theorem instantiate_eq_some_iff (signature : TermSignature) (target : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) (instantiation : TheoremInstance) :
    instantiate? signature target declaration arguments = some instantiation ↔
      Instantiates signature target declaration arguments instantiation := by
  constructor
  · intro success
    by_cases admitted : Substitution.checkAdmissible signature declaration.arguments target arguments = true
    · cases hypotheses : Substitution.substituteList (Substitution.ofList arguments)
          declaration.hypotheses with
      | none => simp [instantiate?, admitted, hypotheses] at success
      | some instHypotheses =>
          cases conclusion : declaration.conclusion.substitute (Substitution.ofList arguments) with
          | none => simp [instantiate?, admitted, hypotheses, conclusion] at success
          | some instConclusion =>
              have same : (⟨instHypotheses, instConclusion⟩ : TheoremInstance) = instantiation := by
                simpa [instantiate?, admitted, hypotheses, conclusion] using success
              subst instantiation
              exact ⟨(Substitution.checkAdmissible_iff _ _ _ _).mp admitted,
                (Substitution.substituteList_eq_some_iff _ _ _).mp hypotheses,
                Preterm.substitute_sound conclusion⟩
    · simp [instantiate?, admitted] at success
  · exact Instantiates.eval

theorem instantiate_none_iff (signature : TermSignature) (target : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) :
    instantiate? signature target declaration arguments = none ↔
      ¬ ∃ instantiation, Instantiates signature target declaration arguments instantiation := by
  constructor
  · intro refused ⟨instantiation, instantiated⟩
    have success := instantiated.eval
    rw [refused] at success
    contradiction
  · intro impossible
    cases result : instantiate? signature target declaration arguments with
    | none => rfl
    | some instantiation =>
        exact False.elim (impossible ⟨instantiation, (instantiate_eq_some_iff _ _ _ _ _).mp result⟩)

theorem Instantiates.deterministic {signature : TermSignature} {target : Context}
    {declaration : TheoremDecl} {arguments : List Preterm} {first second : TheoremInstance}
    (left : Instantiates signature target declaration arguments first)
    (right : Instantiates signature target declaration arguments second) : first = second :=
  Option.some.inj (left.eval.symm.trans right.eval)

end TheoremDecl

mutual

inductive Derives (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm) : Preterm → Prop where
  | hypothesis {expression : Preterm} : expression ∈ hypotheses →
      Derives signature definitions theorems context hypotheses expression
  | theoremApp {index : Nat} {declaration : TheoremDecl} {arguments : List Preterm}
      {instantiation : TheoremInstance} :
      theorems index = some declaration →
      TheoremDecl.Instantiates signature context declaration arguments instantiation →
      DerivesList signature definitions theorems context hypotheses instantiation.hypotheses →
      Derives signature definitions theorems context hypotheses instantiation.conclusion
  | conversion {left right : Preterm} {sort : Nat} :
      Converts signature definitions context left right sort →
      Derives signature definitions theorems context hypotheses left →
      Derives signature definitions theorems context hypotheses right

inductive DerivesList (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm) :
    List Preterm → Prop where
  | nil : DerivesList signature definitions theorems context hypotheses []
  | cons {expression : Preterm} {expressions : List Preterm} :
      Derives signature definitions theorems context hypotheses expression →
      DerivesList signature definitions theorems context hypotheses expressions →
      DerivesList signature definitions theorems context hypotheses (expression :: expressions)

end

theorem derivesList_iff (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses expressions : List Preterm) :
    DerivesList signature definitions theorems context hypotheses expressions ↔
      ∀ expression ∈ expressions, Derives signature definitions theorems context hypotheses expression := by
  induction expressions with
  | nil => constructor <;> intro _; exacts [by simp, .nil]
  | cons expression expressions ih =>
      constructor
      · intro derived value member
        cases derived with
        | cons head tail =>
            rcases List.mem_cons.mp member with rfl | rest
            · exact head
            · exact ih.mp tail value rest
      · intro pointwise
        exact .cons (pointwise expression (by simp))
          (ih.mpr (fun value member => pointwise value (List.mem_cons_of_mem _ member)))

namespace Preterm

/-- Saturated expression of a declared provable sort. -/
def IsStatement (sorts : SortSignature) (signature : TermSignature)
    (context : Context) (expression : Preterm) : Prop :=
  ∃ sort info, HasType signature context expression [] sort ∧
    sorts sort = some info ∧ info.provable = true

theorem IsStatement.substitute {sorts : SortSignature} {signature : TermSignature}
    {formal target : Context} {source result : Preterm} {arguments : List Preterm}
    (statement : IsStatement sorts signature formal source)
    (admitted : Substitution.Admissible signature formal target arguments)
    (substituted : Substitutes (Substitution.ofList arguments) source result) :
    IsStatement sorts signature target result := by
  obtain ⟨sort, info, typed, known, provable⟩ := statement
  exact ⟨sort, info, typed.substitute admitted.typed substituted, known, provable⟩

theorem IsStatement.convert {sorts : SortSignature} {signature : TermSignature}
    {definitions : Definition.Signature} {context : Context} {left right : Preterm} {sort : Nat}
    (statement : IsStatement sorts signature context left)
    (conversion : Converts signature definitions context left right sort) :
    IsStatement sorts signature context right := by
  obtain ⟨oldSort, info, typed, known, provable⟩ := statement
  obtain ⟨leftTyped, rightTyped⟩ := conversion.typed
  have same := (typed.deterministic leftTyped).2
  exact ⟨sort, info, rightTyped, same ▸ known, provable⟩

end Preterm

theorem Derives.statement {sorts : SortSignature} {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature}
    {context : Context} {hypotheses : List Preterm} {expression : Preterm}
    (localStatements : ∀ hypothesis ∈ hypotheses,
      Preterm.IsStatement sorts signature context hypothesis)
    (declarations : ∀ index declaration, theorems index = some declaration →
      Preterm.IsStatement sorts signature declaration.arguments declaration.conclusion)
    (derived : Derives signature definitions theorems context hypotheses expression) :
    Preterm.IsStatement sorts signature context expression := by
  induction derived using Derives.rec
      (motive_2 := fun expressions _ =>
        ∀ expression ∈ expressions, Preterm.IsStatement sorts signature context expression) with
  | hypothesis member => exact localStatements _ member
  | theoremApp lookup instantiation _ _ =>
      exact (declarations _ _ lookup).substitute instantiation.admissible instantiation.conclusion
  | conversion converted _ ih => exact ih.convert converted
  | nil => rename_i value member; cases member
  | cons _ _ ihHead ihTail =>
      rename_i value member
      rcases List.mem_cons.mp member with rfl | member
      · exact ihHead
      · exact ihTail _ member

end Mettapedia.Languages.MM0.Kernel
