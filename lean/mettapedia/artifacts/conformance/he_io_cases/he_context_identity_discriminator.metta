; Equal space contents do not identify mutable contexts.
!(bind! &left-context (new-space))
!(bind! &right-context (new-space))
!(assertEqualToResult (get-atoms &left-context) ())
!(assertEqualToResult (get-atoms &right-context) ())
!(add-atom &left-context (seen Marker))
!(assertEqualToResult (match &left-context (seen $x) $x) (Marker))
!(assertEqualToResult (match &right-context (seen $x) $x) ())
