; Each use of the polymorphic symbol receives its own typing instance.
(: ScopeNil (PolyList $element))
(: cross-inst (-> (PolyList Number) (PolyList String) R))
!(get-type (cross-inst ScopeNil ScopeNil))
(: fresh-r R)
!(let $state (new-state fresh-r)
   (change-state! $state (cross-inst ScopeNil ScopeNil)))
