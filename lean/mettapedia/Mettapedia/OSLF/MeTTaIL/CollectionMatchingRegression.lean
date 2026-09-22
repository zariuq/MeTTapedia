import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Collection matching regression checks

Ordered sequences and bags have different matching laws. These finite examples
exercise ordered vector prefixes and suffixes, permutation-insensitive bags,
and preservation of answer occurrences. They do not certify all authored languages or decide semantic
reachability of a defect across arbitrary executions.

The two element assignments returned below for a bag with one remainder are
neither a defect nor a counterexample to anything: matching a bag is matching
modulo associativity and commutativity, and answering with more than one
solution is what that means.  The unitarity results for sequence variables
concern *ordered* spines with the variable in last position and say nothing
about bags, wherever the remainder sits.  That example is a positive control for
the bag law, not a negative one.
-/

namespace Mettapedia.OSLF.MeTTaIL.CollectionMatchingRegression

open Syntax Match

set_option autoImplicit false

/-- Vectors retain their order rather than inheriting the bag law. -/
theorem reversed_vector_does_not_match :
    matchPattern
      (.collection .vec [.apply "a" [], .apply "b" []] none)
      (.collection .vec [.apply "b" [], .apply "a" []] none)
      = [] := by decide +kernel

theorem equal_vector_matches :
    matchPattern
      (.collection .vec [.apply "a" [], .apply "b" []] none)
      (.collection .vec [.apply "a" [], .apply "b" []] none)
      = [[]] := by decide +kernel

theorem different_vector_elements_do_not_match :
    matchPattern
      (.collection .vec [.apply "a" [], .apply "b" []] none)
      (.collection .vec [.apply "a" [], .apply "c" []] none)
      = [] := by decide +kernel

theorem different_collection_kinds_do_not_match :
    matchPattern
      (.collection .vec [.apply "a" []] none)
      (.collection .hashBag [.apply "a" []] none)
      = [] := by decide +kernel

theorem bag_order_does_not_prevent_matching :
    matchPattern
      (.collection .hashBag [.apply "a" [], .apply "b" []] none)
      (.collection .hashBag [.apply "b" [], .apply "a" []] none)
      = [[]] := by decide +kernel

/-- The two branches bind the element variable to genuinely different atoms. -/
theorem one_remainder_bag_has_distinct_answers :
    (matchPattern
      (.collection .hashBag [.fvar "X"] (some "R"))
      (.collection .hashBag [.apply "a" [], .apply "b" []] none)).map
        (fun bindings => bindings.lookup "X")
      = [some (.apply "a" []), some (.apply "b" [])] := by decide +kernel

theorem vector_remainder_is_the_ordered_suffix :
    (matchPattern
      (.collection .vec [.fvar "X"] (some "R"))
      (.collection .vec [.apply "a" [], .apply "b" [], .apply "c" []] none)).map
        (fun bindings => (bindings.lookup "X", bindings.lookup "R"))
      = [(some (.apply "a" []),
          some (.collection .vec [.apply "b" [], .apply "c" []] none))] := by
  decide +kernel

theorem vector_prefix_cannot_skip_an_element :
    matchPattern
      (.collection .vec [.apply "a" []] (some "R"))
      (.collection .vec [.apply "b" [], .apply "a" []] none)
      = [] := by decide +kernel

theorem vector_prefix_cannot_exceed_the_term :
    matchPattern
      (.collection .vec [.fvar "X", .fvar "Y"] (some "R"))
      (.collection .vec [.apply "a" []] none)
      = [] := by decide +kernel

theorem vector_without_remainder_requires_exact_length :
    matchPattern
      (.collection .vec [.fvar "X"] none)
      (.collection .vec [.apply "a" [], .apply "b" []] none)
      = [] := by decide +kernel

theorem empty_vector_prefix_retains_the_entire_suffix :
    matchPattern
      (.collection .vec [] (some "R"))
      (.collection .vec [.apply "a" [], .apply "b" []] none)
      = [[("R", .collection .vec [.apply "a" [], .apply "b" []] none)]] := by
  decide +kernel

theorem vector_remainder_checks_repeated_binding_consistency :
    matchPattern
      (.collection .vec [.fvar "R"] (some "R"))
      (.collection .vec [.apply "a" [], .apply "b" []] none)
      = [] := by decide +kernel

theorem set_order_does_not_prevent_matching :
    matchPattern
      (.collection .hashSet [.apply "a" [], .apply "b" []] none)
      (.collection .hashSet [.apply "b" [], .apply "a" []] none)
      = [[]] := by decide +kernel

theorem identical_bag_elements_retain_both_answer_occurrences :
    (matchPattern
      (.collection .hashBag [.fvar "X"] (some "R"))
      (.collection .hashBag [.apply "a" [], .apply "a" []] none)).map
        (fun bindings => bindings.lookup "X")
      = [some (.apply "a" []), some (.apply "a" [])] := by decide +kernel

theorem binding_equivalence_does_not_reorder_vectors :
    matchPatternWith (fun _ _ => true)
      (.collection .vec [.apply "a" [], .apply "b" []] none)
      (.collection .vec [.apply "b" [], .apply "a" []] none)
      = [] := by decide +kernel

theorem binding_equivalence_preserves_vector_suffix_type :
    (matchPatternWith (fun first second => first == second)
      (.collection .vec [.fvar "X"] (some "R"))
      (.collection .vec [.apply "a" [], .apply "b" []] none)).map
        (fun bindings => bindings.lookup "R")
      = [some (.collection .vec [.apply "b" []] none)] := by decide +kernel

end Mettapedia.OSLF.MeTTaIL.CollectionMatchingRegression
