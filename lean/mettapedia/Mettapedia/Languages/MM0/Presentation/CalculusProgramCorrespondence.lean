import Mettapedia.Languages.MM0.Presentation.CalculusProgram

/-!
# What the checker of the MM0 calculus computes

Every equation of the checker is followed through the shared engine. The data
of an application built by the program is the data of the instantiated
pattern, argument validity is computed exactly, and the generated rule
equations instantiate exactly the rules of the presentation. A computed leaf
is decided by running the theory's lookup, instantiation or conversion program
to completion, so the program checks a certificate against the specified
checker in which each leaf is settled by its authored relation, whatever fuel
the leaf names.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.MM0.Presentation.ComputationalCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.Languages.MM0.Kernel
open Calculus
open ComputationalContext ComputationalArguments ComputationalProof ComputationalConversion
open ComputationalTyping ComputationalDefinitions

local notation "P" => calculusProgram
local notation "A" => calculusEquations
local notation "H" => dataEqualityHost

/-! ## Dispatch -/

theorem calculus_equation {head : String} {arguments : List Term}
    {equation : DeterministicEquations.Equation} {environment : Env} {result : Term}
    (used : head ∈ calculusEquations.map DeterministicEquations.Equation.head)
    (defined : calculusEquations.definesAt head arguments.length = true)
    (selected : calculusEquations.select head arguments = some (equation, environment))
    (body : Evaluates P H environment equation.body result) :
    Applies P H head arguments result :=
  Applies.suffix_equation calculusEquations_disjoint used defined selected body

theorem proof_reused {head : String} (used : head ∈ proofEquations.calledHeads)
    {arguments : List Term} {result : Term}
    (computed : Applies proofProgram H head arguments result) : Applies P H head arguments result :=
  (Applies.append_iff proofProgram calculusEquations H calculusEquations_disjoint head
    (by
      simp only [proofProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
      exact Or.inr used) arguments result).mpr computed

/-- The equations of one head, when no other block defines it. -/
theorem select_block (before block after : Program) (head : String) (arguments : List Term)
    (outside : before.defines head = false) (later : after.defines head = false) :
    (before ++ block ++ after).select head arguments = block.select head arguments := by
  simp only [Program.select, List.findSome?_append]
  have first := Program.select_none_of_undefined outside arguments
  have last := Program.select_none_of_undefined later arguments
  simp only [Program.select] at first last
  rw [first, last, Option.none_or, Option.or_none]

theorem constructs {environment : Env} {head : String} {sources values : List Term}
    (ordinary : ¬ Special head sources) (undefined : calculusProgram.defines head = false)
    (unhandled : dataEqualityHost.primitive head values = .unhandled)
    (children : List.Forall₂ (Evaluates P H environment) sources values) :
    Evaluates P H environment (.expr (.sym head :: sources)) (.expr (.sym head :: values)) :=
  Evaluates.call ordinary children (.constructor undefined unhandled)

theorem host_lt (left right : Nat) :
    dataEqualityHost.primitive "nik:nat-lt" [natural left, natural right] = .value (boolean (decide (left < right))) := by
  rw [dataEqualityHost_prior _ _ (by decide), productDivisionHost_prior _ _ rfl]
  exact computationalHost_binary (operation := .lt) rfl left right (by decide) (by decide)

theorem host_add (left right : Nat) :
    dataEqualityHost.primitive "nik:nat-add" [natural left, natural right] = .value (natural (left + right)) := by
  rw [dataEqualityHost_prior _ _ (by decide), productDivisionHost_prior _ _ rfl]
  exact computationalHost_binary (operation := .add) rfl left right (by decide) (by decide)

theorem data_eq_computes (left right : Term) :
    Applies P H "nik:data-eq" [left, right] (boolean (decide (left = right))) :=
  data_equality_computes P left right (by rfl)

/-! ## Matching against tagged data -/

theorem matchTerms_length_ne : ∀ {patterns values : List Term},
    patterns.length ≠ values.length → matchTerms patterns values = none
  | [], [], different => absurd rfl different
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | pattern :: patterns, value :: values, different => by
      have rest := matchTerms_length_ne (patterns := patterns) (values := values)
        (by simpa using different)
      simp only [matchTerms, rest]
      cases matchTerm pattern value <;> rfl

theorem matchTerm_tag_none {tag name : String} :
    ∀ {value : Term}, (∀ inner, value ≠ .expr [.sym tag, inner]) →
      matchTerm (.expr [.sym tag, .var name]) value = none
  | .expr [.sym other, inner], different => by
      have : tag ≠ other := fun same => different inner (by rw [same])
      simp [matchTerm, matchTerms, this]
  | .expr [.lit _, _], _ | .expr [.var _, _], _ | .expr [.expr _, _], _
  | .expr [.list _, _], _ => rfl
  | .expr [], _ => rfl
  | .expr [_], _ => matchTerms_length_ne (by simp)
  | .expr (_ :: _ :: _ :: _), _ => matchTerms_length_ne (by simp)
  | .sym _, _ | .lit _, _ | .var _, _ | .list _, _ => rfl

theorem code_data_or (pattern : Pattern) :
    (∃ datum, code pattern = dataCode datum) ∨
      (∀ inner, code pattern ≠ .expr [.sym "Pattern:Data", inner]) := by
  rcases code_shape pattern with found | ⟨items, same⟩ | ⟨other, _⟩
  · exact .inl found
  · exact .inr fun inner => by simp [same, itemsCode]
  · exact .inr other

theorem code_items_or (pattern : Pattern) :
    (∃ items, code pattern = itemsCode items) ∨
      (∀ inner, code pattern ≠ .expr [.sym "Pattern:Items", inner]) := by
  rcases code_shape pattern with ⟨datum, same⟩ | found | ⟨_, other⟩
  · exact .inr fun inner => by simp [same, dataCode]
  · exact .inl found
  · exact .inr other

/-! ## Building pattern data -/

theorem select_cons (arguments : List Term) :
    calculusEquations.select "mm0:pattern-cons" arguments = consEquations.select "mm0:pattern-cons" arguments := by
  have split : A = ruleEquations ++ consEquations ++
      (listEquations ++ validEquations ++ certificateEquations) := by
    simp [calculusEquations, List.append_assoc]
  rw [split]
  exact select_block _ _ _ _ _ (by decide) (by decide)

theorem select_list (arguments : List Term) :
    calculusEquations.select "mm0:pattern-list" arguments = listEquations.select "mm0:pattern-list" arguments := by
  have split : A = (ruleEquations ++ consEquations) ++ listEquations ++
      (validEquations ++ certificateEquations) := by
    simp [calculusEquations, List.append_assoc]
  rw [split]
  exact select_block _ _ _ _ _ (by decide) (by decide)

/-- **The program builds the data of a cons pattern.** -/
theorem pattern_cons_computes (item items : Pattern) :
    Applies P H "mm0:pattern-cons" [code item, code items] (applyCode "cons" [code item, code items]) := by
  rcases code_data_or item with ⟨datum, itemSame⟩ | itemOther
  · rcases code_items_or items with ⟨list, itemsSame⟩ | itemsOther
    · rw [itemSame, itemsSame]
      have built : applyCode "cons" [dataCode datum, itemsCode list] = itemsCode (datum :: list) := by
        simp [applyCode, consOf?, dataCode, itemsCode]
      rw [built]
      refine calculus_equation (equation := consEquations[0]) (by decide) (by rfl)
        (by rw [select_cons]; rfl) ?_
      exact constructs (by simp [Special]) (by rfl) (by rfl)
        (.cons (Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (.primitive (by rfl) rfl)) .nil)
    · have generic : applyCode "cons" [code item, code items] =
          applyGeneric "cons" [code item, code items] := by
        have none : consOf? [code item, code items] = none := by
          cases found : consOf? [code item, code items] with
          | none => rfl
          | some pair =>
              obtain ⟨first, rest⟩ := pair
              have := consOf?_eq_some found
              simp only [List.cons.injEq, and_true] at this
              exact absurd this.2 (itemsOther _)
        simp [applyCode, none]
      rw [generic]
      have selected : calculusEquations.select "mm0:pattern-cons" [code item, code items] =
          some (consEquations[1], [("item", code item), ("items", code items)]) := by
        rw [select_cons]
        refine consEquations_select_other ?_
        rw [itemSame]
        simp only [matchTerms, matchTerm_tag_none itemsOther]
        cases matchTerm (.expr [.sym "Pattern:Data", .var "item"]) (dataCode datum) <;> rfl
      refine calculus_equation (by decide) (by rfl) selected ?_
      exact constructs (by simp [Special]) (by rfl) (by rfl)
        (.cons (.literal _ _ _ _) (.cons (Evaluates.list
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) .nil))
  · have generic : applyCode "cons" [code item, code items] =
        applyGeneric "cons" [code item, code items] := by
      have none : consOf? [code item, code items] = none := by
        cases found : consOf? [code item, code items] with
        | none => rfl
        | some pair =>
            obtain ⟨first, rest⟩ := pair
            have := consOf?_eq_some found
            simp only [List.cons.injEq] at this
            exact absurd this.1 (itemOther _)
      simp [applyCode, none]
    rw [generic]
    have selected : calculusEquations.select "mm0:pattern-cons" [code item, code items] =
        some (consEquations[1], [("item", code item), ("items", code items)]) := by
      rw [select_cons]
      refine consEquations_select_other ?_
      simp [matchTerms, matchTerm_tag_none itemOther]
    refine calculus_equation (by decide) (by rfl) selected ?_
    exact constructs (by simp [Special]) (by rfl) (by rfl)
      (.cons (.literal _ _ _ _) (.cons (Evaluates.list
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) .nil))

/-- **The program builds the data of a list pattern.** -/
theorem pattern_list_computes (items : Pattern) :
    Applies P H "mm0:pattern-list" [code items] (applyCode "list" [code items]) := by
  rcases code_items_or items with ⟨list, same⟩ | other
  · rw [same]
    have built : applyCode "list" [itemsCode list] = dataCode (.list list) := by
      simp [applyCode, itemsOf?, itemsCode]
    rw [built]
    refine calculus_equation (equation := listEquations[0]) (by decide) (by rfl)
      (by rw [select_list]; rfl) ?_
    exact constructs (by simp [Special]) (by rfl) (by rfl) (.cons (.variable (by rfl)) .nil)
  · have generic : applyCode "list" [code items] = applyGeneric "list" [code items] := by
      have none : itemsOf? [code items] = none := by
        cases found : itemsOf? [code items] with
        | none => rfl
        | some list =>
            have := itemsOf?_eq_some found
            simp only [List.cons.injEq, and_true] at this
            exact absurd this (other _)
      simp [applyCode, none]
    rw [generic]
    have selected : calculusEquations.select "mm0:pattern-list" [code items] =
        some (listEquations[1], [("items", code items)]) := by
      rw [select_list]
      exact listEquations_select_other (matchTerm_tag_none other)
    refine calculus_equation (by decide) (by rfl) selected ?_
    exact constructs (by simp [Special]) (by rfl) (by rfl)
      (.cons (.literal _ _ _ _) (.cons (Evaluates.list (.cons (.variable (by rfl)) .nil)) .nil))

/-! ## Validity of arguments -/

theorem argumentValid_all : ∀ (depth : Nat) (patterns : List Pattern),
    (Pattern.isGroundListAt depth patterns && Pattern.hasCanonicalBinderMetadataList patterns) =
      patterns.all (argumentValidAt depth)
  | _, [] => by simp [Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadataList]
  | depth, pattern :: patterns => by
      have rest := argumentValid_all depth patterns
      simp only [Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadataList, List.all_cons,
        argumentValidAt]
      rw [← rest]
      cases Pattern.isGroundAt depth pattern <;> cases Pattern.hasCanonicalBinderMetadata pattern <;> simp

theorem valid_apply (depth : Nat) (head : String) (arguments : List Pattern) :
    argumentValidAt depth (.apply head arguments) = arguments.all (argumentValidAt depth) := by
  rw [← argumentValid_all]
  simp [argumentValidAt, Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata]

theorem both_computes (first second : Bool) :
    Applies P H "mm0:pattern-both" [boolean first, boolean second] (boolean (first && second)) := by
  cases first
  · exact calculus_equation (equation := validEquations[16]) (by decide) (by rfl) (by rfl)
      (.symbol _ _ _ _)
  · exact calculus_equation (equation := validEquations[15]) (by decide) (by rfl) (by rfl)
      (.variable (by rfl))

mutual

/-- **Validity of an argument at a binder depth is computed exactly.** -/
theorem valid_computes : ∀ (pattern : Pattern) (depth : Nat),
    Applies P H "mm0:pattern-valid" [natural depth, code pattern]
      (boolean (argumentValidAt depth pattern))
  | .bvar index, depth => by
      have valid : argumentValidAt depth (.bvar index) = decide (index < depth) := by
        simp [argumentValidAt, Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata]
      rw [valid]
      exact calculus_equation (equation := validEquations[2]) (by decide) (by rfl) (by rfl)
        (Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
          (.primitive (by rfl) (host_lt index depth)))
  | .fvar name, depth => by
      have valid : argumentValidAt depth (.fvar name) = false := by
        simp [argumentValidAt, Pattern.isGroundAt]
      rw [valid]
      exact calculus_equation (equation := validEquations[3]) (by decide) (by rfl) (by rfl)
        (.symbol _ _ _ _)
  | .apply head arguments, depth => by
      rcases applyCode_cases head (codes arguments) with ⟨datum, same⟩ | ⟨items, same⟩ | generic
      · rw [code_argumentValid (pattern := .apply head arguments) depth (.inl ⟨datum, same⟩)]
        show Applies P H _ [natural depth, applyCode head (codes arguments)] _
        rw [same]
        exact calculus_equation (equation := validEquations[0]) (by decide) (by rfl) (by rfl)
          (.symbol _ _ _ _)
      · rw [code_argumentValid (pattern := .apply head arguments) depth (.inr ⟨items, same⟩)]
        show Applies P H _ [natural depth, applyCode head (codes arguments)] _
        rw [same]
        exact calculus_equation (equation := validEquations[1]) (by decide) (by rfl) (by rfl)
          (.symbol _ _ _ _)
      · show Applies P H _ [natural depth, applyCode head (codes arguments)] _
        rw [generic, valid_apply]
        exact calculus_equation (equation := validEquations[4]) (by decide) (by rfl) (by rfl)
          (Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
            (validAll_computes arguments depth))
  | .lambda none body, depth => by
      have valid : argumentValidAt depth (.lambda none body) = argumentValidAt (depth + 1) body := by
        simp [argumentValidAt, Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata]
      rw [valid]
      exact calculus_equation (equation := validEquations[5]) (by decide) (by rfl) (by rfl)
        (Evaluates.call (by simp [Special])
          (.cons (Evaluates.call (by simp [Special])
              (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil))
              (.primitive (by rfl) (host_add depth 1)))
            (.cons (.variable (by rfl)) .nil))
          (valid_computes body (depth + 1)))
  | .lambda (some name) body, depth => by
      have valid : argumentValidAt depth (.lambda (some name) body) = false := by
        simp [argumentValidAt, Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata]
      rw [valid]
      exact calculus_equation (equation := validEquations[6]) (by decide) (by rfl) (by rfl)
        (.symbol _ _ _ _)
  | .multiLambda arity [] body, depth => by
      have valid : argumentValidAt depth (.multiLambda arity [] body) =
          argumentValidAt (depth + arity) body := by
        simp [argumentValidAt, Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata]
      rw [valid]
      exact calculus_equation (equation := validEquations[7]) (by decide) (by rfl) (by rfl)
        (Evaluates.call (by simp [Special])
          (.cons (Evaluates.call (by simp [Special])
              (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
              (.primitive (by rfl) (host_add depth arity)))
            (.cons (.variable (by rfl)) .nil))
          (valid_computes body (depth + arity)))
  | .multiLambda arity (binder :: binders) body, depth => by
      have valid : argumentValidAt depth (.multiLambda arity (binder :: binders) body) = false := by
        simp [argumentValidAt, Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata]
      rw [valid]
      exact calculus_equation (equation := validEquations[8]) (by decide) (by rfl) (by rfl)
        (.symbol _ _ _ _)
  | .subst body replacement, depth => by
      have valid : argumentValidAt depth (.subst body replacement) =
          (argumentValidAt (depth + 1) body && argumentValidAt depth replacement) := by
        simp only [argumentValidAt, Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata]
        cases Pattern.isGroundAt (depth + 1) body <;> cases Pattern.isGroundAt depth replacement <;>
          cases Pattern.hasCanonicalBinderMetadata body <;> simp
      rw [valid]
      exact calculus_equation (equation := validEquations[9]) (by decide) (by rfl) (by rfl)
        (Evaluates.call (by simp [Special])
          (.cons (Evaluates.call (by simp [Special])
              (.cons (Evaluates.call (by simp [Special])
                  (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil))
                  (.primitive (by rfl) (host_add depth 1)))
                (.cons (.variable (by rfl)) .nil))
              (valid_computes body (depth + 1)))
            (.cons (Evaluates.call (by simp [Special])
                (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
                (valid_computes replacement depth)) .nil))
          (both_computes _ _))
  | .collection kind elements none, depth => by
      have valid : argumentValidAt depth (.collection kind elements none) =
          elements.all (argumentValidAt depth) := by
        rw [← argumentValid_all]
        simp only [argumentValidAt, Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata]
        cases Pattern.isGroundListAt depth elements <;> simp
      rw [valid]
      exact calculus_equation (equation := validEquations[10]) (by decide) (by rfl) (by rfl)
        (Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
          (validAll_computes elements depth))
  | .collection kind elements (some rest), depth => by
      have valid : argumentValidAt depth (.collection kind elements (some rest)) = false := by
        simp [argumentValidAt, Pattern.isGroundAt]
      rw [valid]
      exact calculus_equation (equation := validEquations[11]) (by decide) (by rfl) (by rfl)
        (.symbol _ _ _ _)

theorem validAll_computes : ∀ (patterns : List Pattern) (depth : Nat),
    Applies P H "mm0:pattern-valid-all" [natural depth, .list (codes patterns)]
      (boolean (patterns.all (argumentValidAt depth)))
  | [], depth =>
      calculus_equation (equation := validEquations[12]) (by decide) (by rfl) (by rfl)
        (Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) .nil) (.primitive (by rfl) rfl)) .nil))
          (calculus_equation (equation := validEquations[13]) (by decide) (by rfl) (by rfl)
            (.symbol _ _ _ _)))
  | pattern :: patterns, depth => by
      rw [List.all_cons]
      exact calculus_equation (equation := validEquations[12]) (by decide) (by rfl) (by rfl)
        (Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) .nil) (.primitive (by rfl) rfl)) .nil))
          (calculus_equation (equation := validEquations[14]) (by decide) (by rfl) (by rfl)
            (Evaluates.call (by simp [Special])
              (.cons (Evaluates.call (by simp [Special])
                  (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
                  (valid_computes pattern depth))
                (.cons (Evaluates.call (by simp [Special])
                    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
                    (validAll_computes patterns depth)) .nil))
              (both_computes _ _))))

end

/-! ## Rule patterns -/

theorem templateTerms_length : ∀ templates : List Pattern,
    (templateTerms templates).length = templates.length
  | [] => rfl
  | _ :: templates => by simp [templateTerms, templateTerms_length templates]

theorem lookup_zip : ∀ (names : List String) (arguments : List Pattern) (name : String),
    Env.lookup (names.zip (codes arguments)) name =
      ((names.zip arguments).find? (·.1 == name)).map fun entry => code entry.2
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | first :: names, argument :: arguments, name => by
      have rest := lookup_zip names arguments name
      simp only [Env.lookup] at rest ⊢
      simp only [codes, List.zip_cons_cons, List.find?_cons]
      cases first == name
      · exact rest
      · rfl

theorem find_zip_some : ∀ {names : List String} {arguments : List Pattern} {name : String},
    names.length = arguments.length → name ∈ names →
      ∃ argument, (names.zip arguments).find? (·.1 == name) = some (name, argument)
  | [], _, _, _, member => absurd member List.not_mem_nil
  | _ :: _, [], _, length, _ => by simp at length
  | first :: names, argument :: arguments, name, length, member => by
      by_cases same : first = name
      · subst same
        exact ⟨argument, by simp⟩
      · have rest := find_zip_some (names := names) (arguments := arguments) (by simpa using length)
          ((List.mem_cons.mp member).resolve_left (Ne.symm same))
        simpa [same] using rest

mutual

/-- **The generated right side builds the data of an instantiated rule
pattern.** -/
theorem template_evaluates {names : List String} {arguments : List Pattern}
    (length : names.length = arguments.length) :
    ∀ template : Pattern, templateFragment names template = true →
      Evaluates P H (names.zip (codes arguments)) (templateTerm template)
        (code (applyBindings (names.zip arguments) template))
  | .fvar name, fragment => by
      have member : name ∈ names := by simpa [templateFragment] using fragment
      obtain ⟨argument, found⟩ := find_zip_some length member
      have bound : applyBindings (names.zip arguments) (.fvar name) = argument := by
        rw [applyBindings]
        simp [found]
      rw [bound]
      exact Evaluates.variable (by rw [lookup_zip, found]; rfl)
  | .apply head templates, fragment => by
      simp only [templateFragment, Bool.and_eq_true] at fragment
      obtain ⟨notData, rest⟩ := fragment
      have notData : head ∉ ["sym", "lit", "var", "expr"] := by
        intro member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> simp at notData
      have children := templates_evaluate length templates rest
      have bound : applyBindings (names.zip arguments) (.apply head templates) =
          .apply head (templates.map (applyBindings (names.zip arguments))) := by
        rw [applyBindings]
      rw [bound]
      show Evaluates P H _ (applyTemplate head (templateTerms templates))
        (applyCode head (codes (templates.map (applyBindings (names.zip arguments)))))
      have lengths : (codes (templates.map (applyBindings (names.zip arguments)))).length =
          (templateTerms templates).length := by
        simp [codes_length, templateTerms_length]
      unfold applyTemplate
      split_ifs with hlist hcons hnil
      · obtain ⟨rfl, one⟩ := hlist
        rw [templateTerms_length] at one
        obtain ⟨template, rfl⟩ := List.length_eq_one_iff.mp one
        simp only [templateTerms, List.map_cons, List.map_nil, codes] at children
        exact Evaluates.call (by simp [Special]) (.cons (List.forall₂_cons.mp children).1 .nil)
          (pattern_list_computes _)
      · obtain ⟨rfl, two⟩ := hcons
        rw [templateTerms_length] at two
        obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp two
        simp only [templateTerms, List.map_cons, List.map_nil, codes] at children
        obtain ⟨firstEvaluates, children⟩ := List.forall₂_cons.mp children
        obtain ⟨secondEvaluates, -⟩ := List.forall₂_cons.mp children
        exact Evaluates.call (by simp [Special]) (.cons firstEvaluates (.cons secondEvaluates .nil))
          (pattern_cons_computes _ _)
      · obtain ⟨rfl, empty⟩ := hnil
        have : templates = [] := List.length_eq_zero_iff.mp (by rw [← templateTerms_length, empty]; rfl)
        subst this
        have built : applyCode "nil" [] = itemsCode [] := by simp [applyCode]
        show Evaluates P H _ _ (applyCode "nil" [])
        rw [built]
        exact constructs (by simp [Special]) (by rfl) (by rfl) (.cons (Evaluates.list .nil) .nil)
      · rw [applyCode_generic notData (by rw [lengths]; exact hlist) (by rw [lengths]; exact hcons)
          (fun ⟨named, empty⟩ => hnil ⟨named, List.length_eq_zero_iff.mp
            (by rw [← lengths, empty]; rfl)⟩)]
        exact constructs (by simp [Special]) (by rfl) (by rfl)
          (.cons (.literal _ _ _ _) (.cons (Evaluates.list children) .nil))
  | .bvar _, fragment | .lambda _ _, fragment | .multiLambda _ _ _, fragment
  | .subst _ _, fragment | .collection _ _ _, fragment => by simp [templateFragment] at fragment

theorem templates_evaluate {names : List String} {arguments : List Pattern}
    (length : names.length = arguments.length) :
    ∀ templates : List Pattern, templatesFragment names templates = true →
      List.Forall₂ (Evaluates P H (names.zip (codes arguments))) (templateTerms templates)
        (codes (templates.map (applyBindings (names.zip arguments))))
  | [], _ => .nil
  | template :: templates, fragment => by
      simp only [templatesFragment, Bool.and_eq_true] at fragment
      exact .cons (template_evaluates length template fragment.1)
        (templates_evaluate length templates fragment.2)

end

/-! ## Rule instantiation -/

/-- The rule of a name and arity, instantiated at the arguments. -/
def ruleShape (rule : String) (arguments : List Pattern) : Option (List Pattern × Pattern) :=
  (rules.find? fun r => r.id == rule && arguments.length == r.vars.length).map
    fun r => (r.instPremises arguments, r.instConclusion arguments)

def ruleCode : Option (List Pattern × Pattern) → Term
  | none => .sym "None"
  | some (premises, conclusion) =>
      .expr [.sym "Rule:Instance", code conclusion, .list (codes premises)]

/-- **Local rule instantiation of the calculus**: arguments that are all valid
and a rule of that name and arity. -/
theorem instantiateRule?_eq (rule : String) (arguments : List Pattern) :
    instantiateRule? formMM0 ⟨⟨rule⟩, arguments⟩ =
      if arguments.all (argumentValidAt 0) then ruleShape rule arguments else none := by
  cases found : rules.find? (fun r => r.id == rule && arguments.length == r.vars.length) with
  | some r =>
      have member := List.mem_of_find?_eq_some found
      have condition := List.find?_some found
      simp only [Bool.and_eq_true, beq_iff_eq] at condition
      obtain ⟨sameId, length⟩ := condition
      subst sameId
      have key := fun premises conclusion =>
        (instantiateRule?_eq_some_iff_application (definition := formMM0)
          (ruleInstance := ⟨⟨r.id⟩, arguments⟩) (premises := premises) (conclusion := conclusion)).trans
          (ruleApplication_iff formMM0 rules presents.package r member (presents.lookup member)
            arguments premises conclusion)
      simp only [ruleShape, found, Option.map_some]
      split_ifs with valid
      · exact (key _ _).mpr ⟨length, List.all_eq_true.mp valid, rfl, rfl⟩
      · cases application : instantiateRule? formMM0 ⟨⟨r.id⟩, arguments⟩ with
        | none => rfl
        | some result =>
            obtain ⟨premises, conclusion⟩ := result
            exact absurd (List.all_eq_true.mpr ((key premises conclusion).mp application).2.1) valid
  | none =>
      simp only [ruleShape, found, Option.map_none, ite_self]
      cases application : instantiateRule? formMM0 ⟨⟨rule⟩, arguments⟩ with
      | none => rfl
      | some result =>
          obtain ⟨premises, conclusion⟩ := result
          have applied := instantiateRule?_eq_some_iff_application.mp application
          obtain ⟨schema, lookup, _, _, _, _⟩ := applied
          obtain ⟨r, member, -, sameId⟩ := presents.rule_of_lookup lookup
          simp only [RuleId.mk.injEq] at sameId
          subst sameId
          have length := ((ruleApplication_iff formMM0 rules presents.package r member
            (presents.lookup member) arguments premises conclusion).mp
              (instantiateRule?_eq_some_iff_application.mp application)).1
          rw [List.find?_eq_none] at found
          exact absurd (by simp [length]) (found r member)

theorem select_rule_instance (arguments : List Term) :
    calculusEquations.select "mm0:rule-instance" arguments =
      ruleEquations.select "mm0:rule-instance" arguments := by
  have split : calculusEquations = [] ++ ruleEquations ++
      (consEquations ++ listEquations ++ validEquations ++ certificateEquations) := by
    simp [calculusEquations, List.append_assoc]
  rw [split]
  exact select_block _ _ _ _ _ rfl (by decide)

/-- **The generated rule equations instantiate the rule of the requested name
and arity.** -/
theorem ruleInstance_computes (rule : String) (arguments : List Pattern) :
    Applies P H "mm0:rule-instance" [.lit rule, .list (codes arguments)]
      (ruleCode (ruleShape rule arguments)) := by
  have selected : calculusEquations.select "mm0:rule-instance" [.lit rule, .list (codes arguments)] =
      match rules.find? (fun r => r.id == rule && arguments.length == r.vars.length) with
      | some r => some (ruleEquation r, r.vars.zip (codes arguments))
      | none => some (unknownRule, [("rule", .lit rule), ("arguments", .list (codes arguments))]) := by
    rw [select_rule_instance]
    have generated := select_rules rules rule (codes arguments)
    rw [codes_length] at generated
    exact generated
  unfold ruleShape
  cases found : rules.find? (fun r => r.id == rule && arguments.length == r.vars.length) with
  | none =>
      rw [found] at selected
      exact calculus_equation (by decide) (by rfl) selected (.symbol _ _ _ _)
  | some r =>
      rw [found] at selected
      have member := List.mem_of_find?_eq_some found
      have condition := List.find?_some found
      simp only [Bool.and_eq_true, beq_iff_eq] at condition
      obtain ⟨fragmentConclusion, fragmentPremises⟩ := rules_templates r member
      have length : r.vars.length = arguments.length := condition.2.symm
      exact calculus_equation (by decide) (by rfl) selected
        (constructs (by simp [Special]) (by rfl) (by rfl)
          (.cons (template_evaluates length r.conclusion fragmentConclusion)
            (.cons (Evaluates.list (templates_evaluate length r.premises fragmentPremises)) .nil)))

/-! ## Computed leaves -/

/-- Evaluate the argument variables of a call, bound by the selected equation. -/
local macro "bound_variables" : tactic =>
  `(tactic| repeat (first
    | exact List.Forall₂.nil
    | refine List.Forall₂.cons (Evaluates.variable (by rfl)) ?_))

variable (T : Theory)

theorem theory_lookup_computes (index : Nat) :
    Applies P H "nik:nat-table-get" [encodeTheorems T.theorems, natural index]
      (encodeLookupResult ((T.theoremSignature index).map encodeTheorem)) :=
  proof_reused (by decide) (theorem_lookup_computes T.theorems index)

theorem theory_instance_computes (context : Context) (declaration : TheoremDecl)
    (arguments : List Preterm) :
    Applies P H "mm0:instantiate-theorem"
      [encodeTable T.terms, encodeContext context, encodeTheorem declaration, encodeExpressions arguments]
      (encodeInstance (declaration.instantiate? T.termSignature context arguments)) := by
  have run := theorem_instantiation_computes T.terms context declaration arguments
  rw [theory_signature] at run
  exact proof_reused (by decide) run

theorem theory_convert_computes (context : Context) (witness : ConvWitness) :
    Applies P H "mm0:conversion"
      [encodeTable T.terms, encodeDefinitions T.definitions, encodeContext context, encodeWitness witness]
      (encodeConversion (witness.conversion? T.termSignature T.definitionSignature context)) :=
  proof_reused (by decide) (conversion_reused _ (by
    simp only [conversionProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inr (by decide)) _ _ (theory_conversion_computes T context witness))

/-- **A computed leaf settled by its authored relation**, whatever fuel it
names: the lookup, instantiation or conversion of the theory gives the
claimed answer. -/
def settled : (family T).Leaf → Bool
  | ⟨.lookup, ⟨index, declaration, _⟩⟩ =>
      decide ((T.theoremSignature index).map encodeTheorem = some (encodeTheorem declaration))
  | ⟨.instantiate, ⟨(context, declaration, arguments), result, _⟩⟩ =>
      decide (@Eq (Option TheoremInstance) (declaration.instantiate? T.termSignature context arguments)
        (some result))
  | ⟨.convert, ⟨(context, witness), result, _⟩⟩ =>
      decide (@Eq (Option ConversionResult)
        (witness.conversion? T.termSignature T.definitionSignature context) (some result))

/-- The leaf evaluator of the program: the judgment of a settled leaf. -/
def settledEvaluate (leaf : (family T).Leaf) : Option Pattern :=
  if settled T leaf then some ((family T).judgment leaf.1 leaf.2.query leaf.2.answer) else none

theorem check_computed (goal : Pattern) (leaf : (family T).Leaf) :
    check formMM0 (settledEvaluate T) goal (.computed leaf) =
      (settled T leaf && decide ((family T).judgment leaf.1 leaf.2.query leaf.2.answer = goal)) := by
  simp only [check, settledEvaluate]
  by_cases verdict : settled T leaf = true
  · simp [verdict]
  · simp [verdict]

theorem leafVerdict_computes (returned : Bool) (judgment goal : Pattern) :
    Applies P H "mm0:certificate-leaf" [boolean returned, code judgment, code goal]
      (boolean (returned && decide (judgment = goal))) := by
  cases returned
  · exact calculus_equation (equation := certificateEquations[5]) (by decide) (by rfl) (by rfl)
      (.symbol _ _ _ _)
  · have same := data_eq_computes (code judgment) (code goal)
    rw [show decide (code judgment = code goal) = decide (judgment = goal) from
      decide_eq_decide.mpr code_injective.eq_iff] at same
    exact calculus_equation (equation := certificateEquations[4]) (by decide) (by rfl) (by rfl)
      (Evaluates.call (by simp [Special]) (by bound_variables) same)

theorem code_theoremJ (index : Nat) (declaration : TheoremDecl) :
    code (theoremJ index declaration) =
      applyGeneric "mm0:theorem" [dataCode (natural index), dataCode (encodeTheorem declaration)] := by
  simp only [theoremJ, jTheorem, indexPattern, theoremPattern, code, codes, code_termPattern]
  exact applyCode_generic (by decide) (by simp) (by simp) (by simp)

theorem code_instanceJ (context : Context) (declaration : TheoremDecl) (arguments : List Preterm)
    (result : TheoremInstance) :
    code (instanceJ context declaration arguments result) =
      applyGeneric "mm0:instance" [dataCode (encodeContext context), dataCode (encodeTheorem declaration),
        dataCode (encodeExpressions arguments), dataCode (encodeExpressions result.hypotheses),
        dataCode (encode result.conclusion)] := by
  simp only [instanceJ, jInstance, contextPattern, theoremPattern, expressionsPattern,
    expressionPattern, code, codes, code_termPattern]
  exact applyCode_generic (by decide) (by simp) (by simp) (by simp)

theorem code_convertsJ (context : Context) (result : ConversionResult) :
    code (convertsJ context result) =
      applyGeneric "mm0:converts" [dataCode (encodeContext context), dataCode (encode result.left),
        dataCode (encode result.right), dataCode (natural result.sort)] := by
  simp only [convertsJ, jConverts, contextPattern, expressionPattern, indexPattern, code, codes,
    code_termPattern]
  exact applyCode_generic (by decide) (by simp) (by simp) (by simp)

/-- The data of a judgment built inside a leaf equation. -/
theorem judgment_evaluates {environment : Env} {head : String} {names : List String}
    {values : List Term} (found : names.map environment.lookup = values.map some) :
    Evaluates P H environment
      (.expr [.sym "Pattern:Apply", .lit head,
        .list (names.map fun name => .expr [.sym "Pattern:Data", .var name])])
      (applyGeneric head (values.map dataCode)) := by
  refine constructs (by simp [Special]) (by rfl) (by rfl)
    (.cons (.literal _ _ _ _) (.cons (Evaluates.list ?_) .nil))
  induction names generalizing values with
  | nil =>
      cases values with
      | nil => exact .nil
      | cons _ _ => simp at found
  | cons name names ih =>
      cases values with
      | nil => simp at found
      | cons value values =>
          simp only [List.map_cons, List.cons.injEq] at found
          exact .cons (constructs (by simp [Special]) (by rfl) (by rfl)
            (.cons (.variable found.1) .nil)) (ih found.2)

/-- **A computed leaf is checked by running the theory's program.** -/
theorem leaf_computes (goal : Pattern) : ∀ leaf : (family T).Leaf,
    Applies P H "mm0:certificate" (request T goal (.computed leaf))
      (boolean (check formMM0 (settledEvaluate T) goal (.computed leaf)))
  | ⟨.lookup, ⟨index, declaration, fuel⟩⟩ => by
      rw [check_computed]
      have returned := data_eq_computes (encodeLookupResult ((T.theoremSignature index).map encodeTheorem))
        (.expr [.sym "Some", encodeTheorem declaration])
      rw [show decide (encodeLookupResult ((T.theoremSignature index).map encodeTheorem) =
          .expr [.sym "Some", encodeTheorem declaration]) = settled T ⟨.lookup, ⟨index, declaration, fuel⟩⟩ from
        decide_eq_decide.mpr (encodeLookupResult_injective.eq_iff (b := some (encodeTheorem declaration)))]
        at returned
      have verdict := leafVerdict_computes (settled T ⟨.lookup, ⟨index, declaration, fuel⟩⟩)
        (theoremJ index declaration) goal
      rw [code_theoremJ index declaration] at verdict
      refine calculus_equation (equation := certificateEquations[1]) (by decide) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (Evaluates.call (by simp [Special])
            (.cons (Evaluates.call (by simp [Special]) (by bound_variables) (theory_lookup_computes T index))
              (.cons (constructs (by simp [Special]) (by rfl) (by rfl) (by bound_variables)) .nil))
            returned)
          (.cons (judgment_evaluates (names := ["index", "declaration"])
              (values := [natural index, encodeTheorem declaration]) (by rfl))
            (.cons (.variable (by rfl)) .nil)))
        verdict
  | ⟨.instantiate, ⟨(context, declaration, arguments), result, fuel⟩⟩ => by
      rw [check_computed]
      have returned := data_eq_computes
        (encodeInstance (declaration.instantiate? T.termSignature context arguments))
        (.expr [.sym "MM0:Instance", encodeExpressions result.hypotheses, encode result.conclusion])
      rw [show decide (encodeInstance (declaration.instantiate? T.termSignature context arguments) =
          .expr [.sym "MM0:Instance", encodeExpressions result.hypotheses, encode result.conclusion]) =
          settled T ⟨.instantiate, ⟨(context, declaration, arguments), result, fuel⟩⟩ from
        decide_eq_decide.mpr (encodeInstance_injective.eq_iff (b := some result))] at returned
      have verdict := leafVerdict_computes
        (settled T ⟨.instantiate, ⟨(context, declaration, arguments), result, fuel⟩⟩)
        (instanceJ context declaration arguments result) goal
      rw [code_instanceJ context declaration arguments result] at verdict
      refine calculus_equation (equation := certificateEquations[2]) (by decide) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (Evaluates.call (by simp [Special])
            (.cons (Evaluates.call (by simp [Special]) (by bound_variables)
                (theory_instance_computes T context declaration arguments))
              (.cons (constructs (by simp [Special]) (by rfl) (by rfl) (by bound_variables)) .nil))
            returned)
          (.cons (judgment_evaluates
              (names := ["context", "declaration", "arguments", "hypotheses", "conclusion"])
              (values := [encodeContext context, encodeTheorem declaration, encodeExpressions arguments,
                encodeExpressions result.hypotheses, encode result.conclusion]) (by rfl))
            (.cons (.variable (by rfl)) .nil)))
        verdict
  | ⟨.convert, ⟨(context, witness), result, fuel⟩⟩ => by
      rw [check_computed]
      have returned := data_eq_computes
        (encodeConversion (witness.conversion? T.termSignature T.definitionSignature context))
        (.expr [.sym "MM0:Converted", encode result.left, encode result.right, natural result.sort])
      rw [show decide (encodeConversion (witness.conversion? T.termSignature T.definitionSignature context) =
          .expr [.sym "MM0:Converted", encode result.left, encode result.right, natural result.sort]) =
          settled T ⟨.convert, ⟨(context, witness), result, fuel⟩⟩ from
        decide_eq_decide.mpr (encodeConversion_injective.eq_iff (b := some result))] at returned
      have verdict := leafVerdict_computes (settled T ⟨.convert, ⟨(context, witness), result, fuel⟩⟩)
        (convertsJ context result) goal
      rw [code_convertsJ context result] at verdict
      refine calculus_equation (equation := certificateEquations[3]) (by decide) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (Evaluates.call (by simp [Special])
            (.cons (Evaluates.call (by simp [Special]) (by bound_variables)
                (theory_convert_computes T context witness))
              (.cons (constructs (by simp [Special]) (by rfl) (by rfl) (by bound_variables)) .nil))
            returned)
          (.cons (judgment_evaluates (names := ["context", "left", "right", "sort"])
              (values := [encodeContext context, encode result.left, encode result.right,
                natural result.sort]) (by rfl))
            (.cons (.variable (by rfl)) .nil)))
        verdict

/-! ## Children -/

theorem list_view_evaluates {environment : Env} {name : String} {values : List Term}
    (found : environment.lookup name = some (.list values)) :
    Evaluates P H environment (.expr [.sym "nik:list-view", .var name]) (listView values) :=
  Evaluates.call (by simp [Special]) (.cons (.variable found) .nil) (.primitive (by rfl) rfl)

/-- **Children are checked against the premises in order.** -/
theorem children_computes : ∀ (premises : List Pattern) (children : List (CompactProof (family T).Leaf)),
    (∀ child ∈ children, ∀ goal, Applies P H "mm0:certificate" (request T goal child)
      (boolean (check formMM0 (settledEvaluate T) goal child))) →
    Applies P H "mm0:certificate-children"
      (theoryArguments T ++ [.list (codes premises), .list (certificateCodes T children)])
      (boolean (checkChildren formMM0 (settledEvaluate T) premises children))
  | [], [], _ => by
      simp only [checkChildren]
      exact calculus_equation (equation := certificateEquations[12]) (by decide) (by rfl) (by rfl)
        (Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (list_view_evaluates (by rfl)) (.cons (list_view_evaluates (by rfl)) .nil)))))
          (calculus_equation (equation := certificateEquations[13]) (by decide) (by rfl) (by rfl)
            (.symbol _ _ _ _)))
  | [], _ :: _, _ => by
      simp only [checkChildren]
      exact calculus_equation (equation := certificateEquations[12]) (by decide) (by rfl) (by rfl)
        (Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (list_view_evaluates (by rfl)) (.cons (list_view_evaluates (by rfl)) .nil)))))
          (calculus_equation (equation := certificateEquations[15]) (by decide) (by rfl) (by rfl)
            (.symbol _ _ _ _)))
  | _ :: _, [], _ => by
      simp only [checkChildren]
      exact calculus_equation (equation := certificateEquations[12]) (by decide) (by rfl) (by rfl)
        (Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (list_view_evaluates (by rfl)) (.cons (list_view_evaluates (by rfl)) .nil)))))
          (calculus_equation (equation := certificateEquations[15]) (by decide) (by rfl) (by rfl)
            (.symbol _ _ _ _)))
  | premise :: premises, child :: children, each => by
      simp only [checkChildren]
      have first := each child List.mem_cons_self premise
      have rest := children_computes premises children
        fun other member => each other (List.mem_cons_of_mem _ member)
      have continued : ∀ accepted : Bool,
          Applies P H "mm0:certificate-rest"
            ([boolean accepted] ++ theoryArguments T ++
              [.list (codes premises), .list (certificateCodes T children)])
            (boolean (accepted && checkChildren formMM0 (settledEvaluate T) premises children)) := by
        intro accepted
        cases accepted
        · exact calculus_equation (equation := certificateEquations[16]) (by decide) (by rfl) (by rfl)
            (.symbol _ _ _ _)
        · exact calculus_equation (equation := certificateEquations[17]) (by decide) (by rfl) (by rfl)
            (Evaluates.call (by simp [Special]) (by bound_variables) rest)
      exact calculus_equation (equation := certificateEquations[12]) (by decide) (by rfl) (by rfl)
        (Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (list_view_evaluates (by rfl)) (.cons (list_view_evaluates (by rfl)) .nil)))))
          (calculus_equation (equation := certificateEquations[14]) (by decide) (by rfl) (by rfl)
            (Evaluates.call (by simp [Special])
              (.cons (Evaluates.call (by simp [Special]) (by bound_variables) first) (by bound_variables))
              (continued _))))

/-! ## Rule nodes -/

/-- The verdict at a node, from its instantiation. -/
def nodeVerdict (goal : Pattern) (children : List (CompactProof (family T).Leaf)) :
    Option (List Pattern × Pattern) → Bool
  | none => false
  | some (premises, conclusion) =>
      decide (conclusion = goal) && checkChildren formMM0 (settledEvaluate T) premises children

theorem check_node_verdict (goal : Pattern) (rule : String) (arguments : List Pattern)
    (children : List (CompactProof (family T).Leaf)) :
    check formMM0 (settledEvaluate T) goal (.node ⟨⟨rule⟩, arguments⟩ children) =
      nodeVerdict T goal children
        (if arguments.all (argumentValidAt 0) then ruleShape rule arguments else none) := by
  simp only [check]
  rw [instantiateRule?_eq]
  cases (if arguments.all (argumentValidAt 0) then ruleShape rule arguments else none) with
  | none => rfl
  | some pair => obtain ⟨premises, conclusion⟩ := pair; rfl

section Node

variable (goal : Pattern) (rule : String) (arguments : List Pattern)
  (children : List (CompactProof (family T).Leaf))
  (each : ∀ child ∈ children, ∀ goal, Applies P H "mm0:certificate" (request T goal child)
    (boolean (check formMM0 (settledEvaluate T) goal child)))

include each in
theorem conclusion_branch (premises : List Pattern) (agrees : Bool) :
    Applies P H "mm0:certificate-conclusion"
      ([boolean agrees] ++ theoryArguments T ++ [.list (codes premises), .list (certificateCodes T children)])
      (boolean (agrees && checkChildren formMM0 (settledEvaluate T) premises children)) := by
  cases agrees
  · exact calculus_equation (equation := certificateEquations[10]) (by decide) (by rfl) (by rfl)
      (.symbol _ _ _ _)
  · exact calculus_equation (equation := certificateEquations[11]) (by decide) (by rfl) (by rfl)
      (Evaluates.call (by simp [Special]) (by bound_variables) (children_computes T premises children each))

include each in
theorem rule_branch : ∀ shape : Option (List Pattern × Pattern),
    Applies P H "mm0:certificate-rule"
      ([ruleCode shape] ++ theoryArguments T ++ [code goal, .list (certificateCodes T children)])
      (boolean (nodeVerdict T goal children shape))
  | none => calculus_equation (equation := certificateEquations[8]) (by decide) (by rfl) (by rfl)
      (.symbol _ _ _ _)
  | some (premises, conclusion) => by
      have agrees := data_eq_computes (code conclusion) (code goal)
      rw [show decide (code conclusion = code goal) = decide (conclusion = goal) from
        decide_eq_decide.mpr code_injective.eq_iff] at agrees
      exact calculus_equation (equation := certificateEquations[9]) (by decide) (by rfl) (by rfl)
        (Evaluates.call (by simp [Special])
          (.cons (Evaluates.call (by simp [Special]) (by bound_variables) agrees) (by bound_variables))
          (conclusion_branch T children each premises _))

include each in
theorem valid_branch (valid : Bool) :
    Applies P H "mm0:certificate-valid"
      ([boolean valid] ++ theoryArguments T ++
        [code goal, .lit rule, .list (codes arguments), .list (certificateCodes T children)])
      (boolean (nodeVerdict T goal children (if valid then ruleShape rule arguments else none))) := by
  cases valid
  · exact calculus_equation (equation := certificateEquations[7]) (by decide) (by rfl) (by rfl)
      (.symbol _ _ _ _)
  · exact calculus_equation (equation := certificateEquations[6]) (by decide) (by rfl) (by rfl)
      (Evaluates.call (by simp [Special])
        (.cons (Evaluates.call (by simp [Special]) (by bound_variables) (ruleInstance_computes rule arguments))
          (by bound_variables))
        (rule_branch T goal children each _))

include each in
/-- **A rule node is checked by validity, instantiation, the conclusion and its
children.** -/
theorem node_computes :
    Applies P H "mm0:certificate"
      (theoryArguments T ++ [code goal, nodeCode rule arguments (certificateCodes T children)])
      (boolean (check formMM0 (settledEvaluate T) goal (.node ⟨⟨rule⟩, arguments⟩ children))) := by
  rw [check_node_verdict]
  exact calculus_equation (equation := certificateEquations[0]) (by decide) (by rfl) (by rfl)
    (Evaluates.call (by simp [Special])
      (.cons (Evaluates.call (by simp [Special])
          (.cons (.literal _ _ _ _) (.cons (.variable (by rfl)) .nil)) (validAll_computes arguments 0))
        (by bound_variables))
      (valid_branch T goal rule arguments children each _))

end Node

/-! ## Certificates -/

theorem checkChildren_replay (definition : ValidatedCalculusLanguageDef) {Query : Type}
    (evaluate : Query → Option Pattern) :
    ∀ (premises : List Pattern) (children : List RawProof),
      checkChildren definition evaluate premises (children.map .replay) =
        checkRawChildren definition premises children
  | [], [] => by simp [checkChildren, checkRawChildren]
  | [], _ :: _ => by simp [checkChildren, checkRawChildren]
  | _ :: _, [] => by simp [checkChildren, checkRawChildren]
  | premise :: premises, child :: children => by
      simp only [List.map_cons, checkChildren, checkRawChildren, check,
        checkChildren_replay definition evaluate premises children]

theorem check_replay_node (definition : ValidatedCalculusLanguageDef) {Query : Type}
    (evaluate : Query → Option Pattern) (goal : Pattern) (ruleInstance : RuleInstance)
    (children : List RawProof) :
    check definition evaluate goal (.replay (.node ruleInstance children)) =
      check definition evaluate goal (.node ruleInstance (children.map .replay)) := by
  simp only [check, checkRaw]
  cases instantiateRule? definition ruleInstance with
  | none => rfl
  | some result =>
      obtain ⟨premises, conclusion⟩ := result
      simp only [checkChildren_replay]

theorem rawCodes_eq : ∀ children : List RawProof,
    rawCodes children = certificateCodes T (children.map .replay)
  | [] => rfl
  | raw :: raws => by
      simp only [rawCodes, List.map_cons, certificateCodes, certificateCode, rawCodes_eq raws]

mutual

theorem replay_computes : ∀ (raw : RawProof) (goal : Pattern),
    Applies P H "mm0:certificate" (request T goal (.replay raw))
      (boolean (check formMM0 (settledEvaluate T) goal (.replay raw)))
  | .node ⟨⟨rule⟩, arguments⟩ children, goal => by
      rw [check_replay_node]
      have coded : request T goal (.replay (.node ⟨⟨rule⟩, arguments⟩ children)) =
          theoryArguments T ++
            [code goal, nodeCode rule arguments (certificateCodes T (children.map .replay))] := by
        simp only [request, certificateCode, rawCode, rawCodes_eq T children]
      rw [coded]
      exact node_computes T goal rule arguments _ (replays_compute children)

theorem replays_compute : ∀ children : List RawProof,
    ∀ child ∈ children.map CompactProof.replay, ∀ goal,
      Applies P H "mm0:certificate" (request T goal child)
        (boolean (check formMM0 (settledEvaluate T) goal child))
  | [], _, member, _ => absurd member List.not_mem_nil
  | raw :: raws, child, member, goal => by
      rcases List.mem_cons.mp member with same | inRest
      · rw [same]
        exact replay_computes raw goal
      · exact replays_compute raws child inRest goal

end

mutual

/-- **The checker computes the verdict of the shared checker with settled
leaves**, for every goal and every certificate. -/
theorem certificate_computes (goal : Pattern) : ∀ proof : CompactProof (family T).Leaf,
    Applies P H "mm0:certificate" (request T goal proof)
      (boolean (check formMM0 (settledEvaluate T) goal proof))
  | .replay raw => replay_computes T raw goal
  | .computed leaf => leaf_computes T goal leaf
  | .node ⟨⟨rule⟩, arguments⟩ children =>
      node_computes T goal rule arguments children (certificates_compute children)

theorem certificates_compute : ∀ children : List (CompactProof (family T).Leaf),
    ∀ child ∈ children, ∀ goal,
      Applies P H "mm0:certificate" (request T goal child)
        (boolean (check formMM0 (settledEvaluate T) goal child))
  | [], _, member, _ => absurd member List.not_mem_nil
  | first :: rest, child, member, goal => by
      rcases List.mem_cons.mp member with same | inRest
      · rw [same]
        exact certificate_computes goal first
      · exact certificates_compute rest child inRest goal

end

end Mettapedia.Languages.MM0.Presentation.ComputationalCalculus
