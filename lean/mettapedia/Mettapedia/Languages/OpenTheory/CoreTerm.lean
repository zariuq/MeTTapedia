import Mettapedia.Languages.OpenTheory.Sequent

/-!
# Executable typed term views for OpenTheory core rules

This module isolates the two partial term operations needed by the first
nonbinding OpenTheory rule tranche: typed application and recognition or
construction of the exact primitive equality form.  Their declarative
relations are stated independently of the executable functions.

Equality recognition checks the full undefined primitive constant, its exact
`A -> A -> bool` annotation, and both operand types.  A constant that merely
prints as `=` cannot pass this boundary.
-/

namespace Mettapedia.Languages.OpenTheory

namespace CanonicalTerm

/-! ## Rechecking closed de Bruijn subterms -/

/-- Check an arbitrary closed de Bruijn term and retain its inferred type. -/
def ofDB? (term : DBTerm) : Option CanonicalTerm :=
  match hchecked : term.inferType [] with
  | some ty => some ⟨term, ty, hchecked⟩
  | none => none

/-- Rechecking the term of an existing canonical term returns that exact
proof-independent value. -/
@[simp] theorem ofDB?_term (term : CanonicalTerm) :
    ofDB? term.term = some term := by
  unfold ofDB?
  split
  · apply congrArg some
    apply CanonicalTerm.ext_term
    rfl
  · rename_i hnone
    rw [term.checked] at hnone
    contradiction

/-- Exact success condition for closed de Bruijn rechecking. -/
theorem ofDB?_eq_some_iff (term : DBTerm) (result : CanonicalTerm) :
    ofDB? term = some result ↔ result.term = term := by
  constructor
  · intro hresult
    unfold ofDB? at hresult
    split at hresult
    · exact congrArg CanonicalTerm.term (Option.some.inj hresult) |>.symm
    · contradiction
  · intro hterm
    subst term
    exact ofDB?_term result

/-! ## Typed application -/

/-- Declarative graph of well-typed canonical application. -/
def ApplicationSemantics
    (function argument result : CanonicalTerm) : Prop :=
  ∃ domain codomain,
    function.ty.destFunction? = some (domain, codomain) ∧
      domain = argument.ty ∧
      result.term = .app function.term argument.term

/-- Apply one checked canonical function to one checked canonical argument. -/
def apply? (function argument : CanonicalTerm) : Option CanonicalTerm :=
  match hfunction : function.ty.destFunction? with
  | some (domain, codomain) =>
      if hargument : Ty.same domain argument.ty then
        some
          ⟨.app function.term argument.term, codomain, by
            simp [DBTerm.inferType, function.checked, argument.checked,
              hfunction, hargument]⟩
      else
        none
  | none => none

/-- Executable application is exactly its independently stated typed graph. -/
theorem apply?_eq_some_iff
    (function argument result : CanonicalTerm) :
    function.apply? argument = some result ↔
      ApplicationSemantics function argument result := by
  constructor
  · intro hresult
    unfold apply? at hresult
    split at hresult
    · rename_i domain codomain hfunction
      split at hresult
      · rename_i hargument
        have hresultEq := Option.some.inj hresult
        have hterm : result.term = .app function.term argument.term := by
          rw [← hresultEq]
        exact ⟨domain, codomain, hfunction,
          (Ty.same_eq_true_iff domain argument.ty).mp hargument, hterm⟩
      · contradiction
    · contradiction
  · rintro ⟨domain, codomain, hfunction, hdomain, hterm⟩
    have hargument : Ty.same domain argument.ty = true :=
      (Ty.same_eq_true_iff domain argument.ty).2 hdomain
    unfold apply?
    split
    · rename_i domain' codomain' hfunction'
      have hpairs : (domain', codomain') = (domain, codomain) :=
        Option.some.inj (hfunction'.symm.trans hfunction)
      cases hpairs
      split
      · apply congrArg some
        apply CanonicalTerm.ext_term
        exact hterm.symm
      · rename_i hreject
        exact (hreject hargument).elim
    · rename_i hreject
      rw [hfunction] at hreject
      contradiction

/-! ## Primitive equality construction -/

/-- The exact de Bruijn shape of primitive equality at one operand type. -/
def equalityDB (operand : Ty) (left right : DBTerm) : DBTerm :=
  .app
    (.app (.const Const.equality (Ty.equality operand)) left)
    right

/-- Declarative graph of primitive equality construction. -/
def EqualityConstructionSemantics
    (left right result : CanonicalTerm) : Prop :=
  left.ty = right.ty ∧
    result.term = equalityDB left.ty left.term right.term

/-- Construct primitive equality only for operands of the same type. -/
def mkEquality? (left right : CanonicalTerm) : Option CanonicalTerm :=
  if htypes : Ty.same left.ty right.ty then
    some
      ⟨equalityDB left.ty left.term right.term, Ty.bool, by
        simp [equalityDB, Ty.equality, Ty.function, TypeOp.function,
          Ty.destFunction?, DBTerm.inferType, left.checked, right.checked,
          htypes]⟩
  else
    none

/-- Executable equality construction is exactly its structural typed graph. -/
theorem mkEquality?_eq_some_iff
    (left right result : CanonicalTerm) :
    mkEquality? left right = some result ↔
      EqualityConstructionSemantics left right result := by
  constructor
  · intro hresult
    unfold mkEquality? at hresult
    split at hresult
    · rename_i htypes
      have hresultEq := Option.some.inj hresult
      constructor
      · exact (Ty.same_eq_true_iff left.ty right.ty).mp htypes
      · rw [← hresultEq]
    · contradiction
  · rintro ⟨htypes, hterm⟩
    have hsame : Ty.same left.ty right.ty = true :=
      (Ty.same_eq_true_iff left.ty right.ty).2 htypes
    unfold mkEquality?
    split
    · apply congrArg some
      apply CanonicalTerm.ext_term
      exact hterm.symm
    · rename_i hreject
      exact (hreject hsame).elim

/-- Every declaratively constructed primitive equality has primitive Boolean
type, independently of its operand type. -/
theorem EqualityConstructionSemantics.resultIsBool
    {left right result : CanonicalTerm}
    (construction : EqualityConstructionSemantics left right result) :
    result.IsBool := by
  have accepted :=
    (mkEquality?_eq_some_iff left right result).mpr construction
  unfold mkEquality? at accepted
  split at accepted
  · have hresult := Option.some.inj accepted
    rw [← hresult]
    rfl
  · contradiction

/-! ## Primitive equality recognition -/

/-- Independent structural semantics of an equality view. -/
def EqualityViewSemantics
    (whole left right : CanonicalTerm) : Prop :=
  left.ty = right.ty ∧
    whole.term = equalityDB left.ty left.term right.term

/-- Recognize the exact primitive equality head and return checked operands. -/
def destEquality? (whole : CanonicalTerm) :
    Option (CanonicalTerm × CanonicalTerm) :=
  match whole.term with
  | .app (.app (.const constant annotation) leftDB) rightDB => do
      let left ← ofDB? leftDB
      let right ← ofDB? rightDB
      if Const.same constant Const.equality &&
          Ty.same annotation (Ty.equality left.ty) &&
          Ty.same left.ty right.ty then
        some (left, right)
      else
        none
  | _ => none

/-- Exact primitive equality recognition, including constant provenance and
the complete type annotation. -/
theorem destEquality?_eq_some_iff
    (whole left right : CanonicalTerm) :
    whole.destEquality? = some (left, right) ↔
      EqualityViewSemantics whole left right := by
  constructor
  · intro hresult
    unfold destEquality? at hresult
    cases hshape : whole.term with
    | const constant annotation => simp [hshape] at hresult
    | free sourceVar => simp [hshape] at hresult
    | bound index => simp [hshape] at hresult
    | abs domain body => simp [hshape] at hresult
    | app outer rightDB =>
        cases houter : outer with
        | const constant annotation => simp [hshape, houter] at hresult
        | free sourceVar => simp [hshape, houter] at hresult
        | bound index => simp [hshape, houter] at hresult
        | abs domain body => simp [hshape, houter] at hresult
        | app head leftDB =>
            cases hhead : head with
            | free sourceVar => simp [hshape, houter, hhead] at hresult
            | bound index => simp [hshape, houter, hhead] at hresult
            | app function argument => simp [hshape, houter, hhead] at hresult
            | abs domain body => simp [hshape, houter, hhead] at hresult
            | const constant annotation =>
                simp only [hshape, houter, hhead] at hresult
                cases hleft : ofDB? leftDB with
                | none => simp [hleft] at hresult
                | some decodedLeft =>
                    cases hright : ofDB? rightDB with
                    | none => simp [hleft, hright] at hresult
                    | some decodedRight =>
                        simp [hleft, hright] at hresult
                        rcases hresult with
                          ⟨⟨⟨hconstant, hannotation⟩, htypes⟩,
                            hdecodedLeft, hdecodedRight⟩
                        subst decodedLeft
                        subst decodedRight
                        have hleftTerm :=
                          (ofDB?_eq_some_iff leftDB left).mp hleft
                        have hrightTerm :=
                          (ofDB?_eq_some_iff rightDB right).mp hright
                        subst constant
                        subst annotation
                        exact ⟨htypes, by
                          simp [equalityDB, hshape, houter, hhead,
                            hleftTerm, hrightTerm]⟩
  · rintro ⟨htypes, hshape⟩
    unfold destEquality?
    rw [hshape]
    simp [equalityDB, ofDB?_term, htypes]

/-- An exact primitive equality has a unique pair of canonical operands. -/
theorem EqualityViewSemantics.unique
    {whole left₁ right₁ left₂ right₂ : CanonicalTerm}
    (first : EqualityViewSemantics whole left₁ right₁)
    (second : EqualityViewSemantics whole left₂ right₂) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  have firstAccepted :=
    (destEquality?_eq_some_iff whole left₁ right₁).mpr first
  have secondAccepted :=
    (destEquality?_eq_some_iff whole left₂ right₂).mpr second
  exact Prod.mk.inj
    (Option.some.inj (firstAccepted.symm.trans secondAccepted))

end CanonicalTerm

/-! ## Calibration examples -/

namespace CoreTermExamples

open SequentExamples

def functionVariable (component : String) (domain codomain : Ty) : CanonicalTerm :=
  ⟨.free ⟨Name.global component, .function domain codomain⟩,
    .function domain codomain, by simp⟩

example :
    ((functionVariable "f" Examples.individual Ty.bool).apply?
      (individualVariable "x")).isSome = true := by
  rw [Option.isSome_iff_exists]
  let result : CanonicalTerm :=
    ⟨.app (functionVariable "f" Examples.individual Ty.bool).term
        (individualVariable "x").term,
      Ty.bool, by
        simp [functionVariable, individualVariable,
          Ty.destFunction?_function]⟩
  refine ⟨result, (CanonicalTerm.apply?_eq_some_iff _ _ _).2 ?_⟩
  refine ⟨Examples.individual, Ty.bool, ?_, ?_, ?_⟩
  · exact Ty.destFunction?_function Examples.individual Ty.bool
  · rfl
  · rfl

/-- Applying a non-function canonical term rejects. -/
example :
    (individualVariable "f").apply? (individualVariable "x") = none := by
  simp [CanonicalTerm.apply?, individualVariable, Ty.destFunction?,
    Examples.individual]

/-- Applying a function to an argument of the wrong domain rejects. -/
example :
    (functionVariable "f" Examples.individual Ty.bool).apply?
      (boolVariable "p") = none := by
  cases hresult :
      (functionVariable "f" Examples.individual Ty.bool).apply?
        (boolVariable "p") with
  | none => rfl
  | some result =>
      exfalso
      rcases (CanonicalTerm.apply?_eq_some_iff _ _ _).mp hresult with
        ⟨domain, codomain, hfunction, hdomain, _⟩
      have hknown :
          (functionVariable "f" Examples.individual Ty.bool).ty.destFunction? =
            some (Examples.individual, Ty.bool) :=
        Ty.destFunction?_function Examples.individual Ty.bool
      have hpairs : (domain, codomain) = (Examples.individual, Ty.bool) :=
        Option.some.inj (hfunction.symm.trans hknown)
      cases hpairs
      simp [boolVariable, Examples.individual, Ty.bool, TypeOp.bool,
        Name.global] at hdomain

def primitiveEquality : CanonicalTerm :=
  ⟨CanonicalTerm.equalityDB Ty.bool
      (boolVariable "p").term (boolVariable "q").term,
    Ty.bool, by
      simp [CanonicalTerm.equalityDB, Ty.equality, Ty.function,
        TypeOp.function, Ty.destFunction?, boolVariable]⟩

example :
    primitiveEquality.destEquality? =
      some (boolVariable "p", boolVariable "q") := by
  apply (CanonicalTerm.destEquality?_eq_some_iff _ _ _).2
  constructor
  · rfl
  · simp [primitiveEquality, CanonicalTerm.equalityDB, boolVariable]

private def printedEqualityImpostor : Const :=
  .mk (Name.global "=") (.defined (.var (Name.global "definition") Ty.bool))

/-- A same-named defined constant is not primitive equality. -/
def impostorEquality : CanonicalTerm :=
  ⟨.app
      (.app (.const printedEqualityImpostor (Ty.equality Ty.bool))
        (boolVariable "p").term)
      (boolVariable "q").term,
    Ty.bool, by
      simp [Ty.equality,
        Ty.function, TypeOp.function, Ty.destFunction?, boolVariable]⟩

theorem impostorEquality_destEquality_eq_none :
    impostorEquality.destEquality? = none := by
  simp [CanonicalTerm.destEquality?, impostorEquality,
    printedEqualityImpostor, Const.equality, Const.same,
    ConstProvenance.same]

/-- A primitive equality head with a well-typed but non-equality annotation is
also rejected. -/
def wrongAnnotationEquality : CanonicalTerm :=
  ⟨.app
      (.app
        (.const Const.equality
          (.function Examples.individual (.function Ty.bool Ty.bool)))
        (individualVariable "x").term)
      (boolVariable "p").term,
    Ty.bool, by
      simp [Ty.function, TypeOp.function, Ty.destFunction?,
        individualVariable, boolVariable]⟩

private def headAnnotation? : DBTerm → Option Ty
  | .app (.app (.const _ annotation) _) _ => some annotation
  | _ => none

theorem wrongAnnotationEquality_destEquality_eq_none :
    wrongAnnotationEquality.destEquality? = none := by
  cases hresult : wrongAnnotationEquality.destEquality? with
  | none => rfl
  | some operands =>
      rcases operands with ⟨left, right⟩
      exfalso
      have hview :=
        (CanonicalTerm.destEquality?_eq_some_iff _ _ _).mp hresult
      have hannotation := congrArg headAnnotation? hview.2
      simp [headAnnotation?, wrongAnnotationEquality,
        CanonicalTerm.equalityDB, Ty.equality, Ty.function,
        TypeOp.function, Examples.individual, Ty.bool, TypeOp.bool,
        Name.global] at hannotation
      have himpossible := hannotation.1.trans hannotation.2.symm
      simp at himpossible

end CoreTermExamples

end Mettapedia.Languages.OpenTheory
