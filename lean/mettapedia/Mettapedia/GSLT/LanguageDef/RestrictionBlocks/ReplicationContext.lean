import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationEquivariance

/-!
# Contexts read fillings through their canonical blocks

The canonical block of an object term depends on a part only through the part's canonical block, and, for an
abstraction under the restriction, through the canonical block of its body: fillings with one canonical block, both
abstractions with one binder and bodies of one canonical block or neither an abstraction, give one canonical block
in every context (`fills_context`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)

variable {block : ReplicationBlock}

/-! ## A constructor reads its arguments' canonical blocks -/

/-- What a constructor of one argument other than an abstraction makes of the argument's canonical block: a
replication collects its molecules, an empty named multiset whose empty instance is the unit is inaction, any other
is one component. -/
def singleOf (block : ReplicationBlock) (label : String) (form : Prenex) : Prenex :=
  if label = block.replicate then normal block ⟨0, replicatedOf block (canonicalOf block) form⟩
  else if label ∈ block.emptyUnits ∧ form = Prenex.nil then Prenex.nil
  else Prenex.atom (.apply label [objectArgument block label form])

/-- **A constructor of one object argument other than an abstraction reads the argument's canonical block.** -/
theorem canonP_single {label : String} {argument : Pattern} (notLambda : ∀ binder body, argument ≠ .lambda binder body)
    (object : isObjectPattern argument = true) :
    canonP block (.apply label [argument]) = singleOf block label (canonP block argument) := by
  unfold singleOf
  by_cases isReplicate : label = block.replicate
  · subst isReplicate
    rw [if_pos rfl, canonP_replicate notLambda]
  rw [if_neg isReplicate]
  by_cases empty : label ∈ block.emptyUnits ∧ canonP block argument = Prenex.nil
  · rw [if_pos empty, canonP_empty empty.1 isReplicate notLambda empty.2]
  rw [if_neg empty, canonP_apply (by simp)
    (fun binder body equal => notLambda binder body (by simpa using equal.2))
    (fun other _ equal => isReplicate equal.1)
    (fun other _ equal listed nil => by
      simp only [List.cons.injEq, and_true] at equal
      subst equal
      exact empty ⟨listed, nil⟩)]
  simp [canonsP, argumentOf_eq_objectArgument object]

theorem argumentOf_lambda {label : String} {binder : Option String} {body : Pattern} {form : Prenex} :
    argumentOf block label (.lambda binder body) form = objectArgument block label form := by
  unfold argumentOf objectArgument
  split_ifs <;> rfl

/-- **A binder other than the restriction is one component**, reading the abstraction's canonical block. -/
theorem canonP_apply_lambda {label : String} {binder : Option String} {body : Pattern}
    (notRestrict : label ≠ block.restrict) :
    canonP block (.apply label [.lambda binder body]) =
      Prenex.atom (.apply label [objectArgument block label (canonP block (.lambda binder body))]) := by
  rw [canonP_apply (by simp) (fun _ _ equal => notRestrict equal.1)
    (fun _ notLambda equal => by
      simp only [List.cons.injEq, and_true] at equal
      exact notLambda _ _ equal.2.symm)
    (fun _ notLambda equal => by
      simp only [List.cons.injEq, and_true] at equal
      exact absurd equal.symm (notLambda _ _))]
  simp [canonsP, argumentOf_lambda]

/-- **A constructor of two object arguments or more is one component**, reading its arguments' canonical blocks. -/
theorem canonP_many {label : String} {arguments : List Pattern} (two : 2 ≤ arguments.length)
    (object : ∀ argument ∈ arguments, isObjectPattern argument = true) :
    canonP block (.apply label arguments) =
      Prenex.atom (.apply label (arguments.map fun argument => objectArgument block label (canonP block argument))) := by
  obtain ⟨first, second, rest, rfl⟩ : ∃ first second rest, arguments = first :: second :: rest := by
    match arguments, two with
    | first :: second :: rest, _ => exact ⟨first, second, rest, rfl⟩
  rw [canonP_apply (by simp) (by simp) (by simp) (by simp), canonsP_eq_map,
    zipWith_map_self _ _ _ _ fun argument member => argumentOf_eq_objectArgument (object argument member)]

/-! ## Fillings no context tells apart -/

theorem apply_notLambda (label : String) (arguments : List Pattern) :
    ∀ binder body, Pattern.apply label arguments ≠ .lambda binder body := fun _ _ equal => by cases equal

theorem multiLambda_notLambda (arity : Nat) (binders : List String) (inner : Pattern) :
    ∀ binder body, Pattern.multiLambda arity binders inner ≠ .lambda binder body := fun _ _ equal => by cases equal

theorem collection_notLambda (kind : CollType) (elements : List Pattern) (rest : Option String) :
    ∀ binder body, Pattern.collection kind elements rest ≠ .lambda binder body := fun _ _ equal => by cases equal

/-- **Fillings no context tells apart**: one canonical block, and both abstractions with one binder and bodies of
one canonical block, or neither an abstraction. -/
def Fills (block : ReplicationBlock) (first second : Pattern) : Prop :=
  canonP block first = canonP block second ∧
    (((∀ binder body, first ≠ .lambda binder body) ∧ ∀ binder body, second ≠ .lambda binder body) ∨
      ∃ binder firstBody secondBody, first = .lambda binder firstBody ∧ second = .lambda binder secondBody ∧
        canonP block firstBody = canonP block secondBody)

/-- **Every context reads interchangeable object fillings alike.** -/
theorem fills_context (context : OneHoleContext) : ∀ {first second : Pattern}, Fills block first second →
    isObjectPattern (context.fill first) = true → isObjectPattern (context.fill second) = true →
      Fills block (context.fill first) (context.fill second) := by
  induction context with
  | hole => exact fun fills _ _ => fills
  | apply constructor before inner after recurse =>
      intro first second fills firstObject secondObject
      have innerFirst := isObject_apply_member firstObject
      have innerSecond := isObject_apply_member secondObject
      obtain ⟨same, shape⟩ := recurse fills innerFirst innerSecond
      simp only [OneHoleContext.fill] at firstObject secondObject ⊢
      refine ⟨?_, .inl ⟨apply_notLambda _ _, apply_notLambda _ _⟩⟩
      by_cases single : before = [] ∧ after = []
      · obtain ⟨rfl, rfl⟩ := single
        simp only [List.nil_append]
        rcases shape with ⟨firstNotLambda, secondNotLambda⟩ |
          ⟨binder, firstBody, secondBody, firstIs, secondIs, bodies⟩
        · rw [canonP_single firstNotLambda innerFirst, canonP_single secondNotLambda innerSecond, same]
        · rw [firstIs, secondIs]
          by_cases isRestrict : constructor = block.restrict
          · subst isRestrict
            rw [canonP_restrict, canonP_restrict, bodies]
          · rw [canonP_apply_lambda isRestrict, canonP_apply_lambda isRestrict, ← firstIs, ← secondIs, same]
      · have nonempty : before ≠ [] ∨ after ≠ [] := by
          by_cases emptyBefore : before = []
          · exact .inr fun emptyAfter => single ⟨emptyBefore, emptyAfter⟩
          · exact .inl emptyBefore
        have two : ∀ middle : Pattern, 2 ≤ (before ++ middle :: after).length := by
          intro middle
          rw [List.length_append, List.length_cons]
          rcases nonempty with nonempty | nonempty
          · have := List.length_pos_of_ne_nil nonempty
            omega
          · have := List.length_pos_of_ne_nil nonempty
            omega
        have objects : ∀ middle : Pattern, isObjectPattern (.apply constructor (before ++ middle :: after)) = true →
            ∀ argument ∈ before ++ middle :: after, isObjectPattern argument = true := by
          intro middle object argument member
          simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true] at object
          exact object argument member
        rw [canonP_many (two _) (objects _ firstObject), canonP_many (two _) (objects _ secondObject)]
        simp only [List.map_append, List.map_cons, same]
  | lambda binder inner recurse =>
      intro first second fills firstObject secondObject
      simp only [OneHoleContext.fill] at firstObject secondObject ⊢
      have innerFirst : isObjectPattern (inner.fill first) = true := by simpa [isObjectPattern] using firstObject
      have innerSecond : isObjectPattern (inner.fill second) = true := by simpa [isObjectPattern] using secondObject
      obtain ⟨same, _⟩ := recurse fills innerFirst innerSecond
      exact ⟨by rw [canonP_lambda, canonP_lambda, same], .inr ⟨binder, _, _, rfl, rfl, same⟩⟩
  | multiLambda arity binders inner recurse =>
      intro first second fills firstObject secondObject
      simp only [OneHoleContext.fill] at firstObject secondObject ⊢
      have innerFirst : isObjectPattern (inner.fill first) = true := by simpa [isObjectPattern] using firstObject
      have innerSecond : isObjectPattern (inner.fill second) = true := by simpa [isObjectPattern] using secondObject
      obtain ⟨same, _⟩ := recurse fills innerFirst innerSecond
      have atomIs : ∀ body, canonP block (.multiLambda arity binders body) =
          Prenex.atom (.multiLambda arity binders (Prenex.toPattern block.toBlock (canonP block body))) := fun _ => by
        simp [canonP]
      exact ⟨by rw [atomIs, atomIs, same], .inl ⟨multiLambda_notLambda _ _ _, multiLambda_notLambda _ _ _⟩⟩
  | substBody inner replacement _ =>
      intro first second _ firstObject _
      simp [OneHoleContext.fill, isObjectPattern] at firstObject
  | substReplacement body inner _ =>
      intro first second _ firstObject _
      simp [OneHoleContext.fill, isObjectPattern] at firstObject
  | collection kind before inner after rest recurse =>
      intro first second fills firstObject secondObject
      have innerFirst := isObject_collection_member firstObject
      have innerSecond := isObject_collection_member secondObject
      obtain ⟨same, _⟩ := recurse fills innerFirst innerSecond
      simp only [OneHoleContext.fill] at firstObject secondObject ⊢
      refine ⟨?_, .inl ⟨collection_notLambda _ _ _, collection_notLambda _ _ _⟩⟩
      have closed : rest = none := by
        cases rest with
        | none => rfl
        | some name => simp [isObjectPattern] at firstObject
      subst closed
      cases kind with
      | hashBag =>
          rw [canonP_bag, canonP_bag, canonsP_eq_map, canonsP_eq_map]
          simp only [List.map_append, List.map_cons, same]
      | hashSet =>
          have atomIs : ∀ list : List Pattern, canonP block (.collection .hashSet list none) =
              Prenex.atom (.collection .hashSet ((list.map (canonP block)).map (Prenex.toPattern block.toBlock))
                none) := fun list => by
            simp [canonP, canonsP_eq_map]
          rw [atomIs, atomIs]
          simp only [List.map_append, List.map_cons, same]
      | vec =>
          have atomIs : ∀ list : List Pattern, canonP block (.collection .vec list none) =
              Prenex.atom (.collection .vec ((list.map (canonP block)).map (Prenex.toPattern block.toBlock))
                none) := fun list => by
            simp [canonP, canonsP_eq_map]
          rw [atomIs, atomIs]
          simp only [List.map_append, List.map_cons, same]

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
