% External oracle for the two source query modes. Load after PeTTa's metta.pl.
% The corresponding finite-query claims are in MainlineTypeQueryModes.lean
% and MainlineTypeQueryEnumeration.lean.

type_query_mode_controls :-
    findall(T, 'get-type'(3, T), ['Number']),
    'get-type'(3, '%Undefined%'),
    \+ 'get-type'(3, 'Unrelated'),
    'add-atom'('&self', [':', 3, 'Special'], _),
    'get-type'(3, 'Special'),
    findall(T, 'get-type'(3, T), ['Number']),
    'add-atom'('&self', [':', wildcard, ['->', '%Undefined%', 'C']], _),
    findall(T, 'get-type'([wildcard, 3], T), ['C']),
    'add-atom'('&self', [':', repeated, 'A'], _),
    'add-atom'('&self', [':', repeated, 'A'], _),
    'add-atom'('&self', [':', repeated_function, ['->', 'A', 'C']], _),
    findall(T, 'get-type'([repeated_function, repeated], T), ['C', 'C']),
    writeln('PASS: fresh output, bound output, primitive cuts and bound recursive arguments').
