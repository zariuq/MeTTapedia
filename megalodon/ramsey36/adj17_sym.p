% Minimal TPTP for Adj17 symmetry
% Only the essential parts: Adj17 definition and the conjecture

% Declare 17 distinct constants for vertices 0-16
fof(distinct_vertices, axiom,
  c0 != c1 & c0 != c2 & c0 != c3 & c0 != c4 & c0 != c5 & c0 != c6 & c0 != c7 &
  c0 != c8 & c0 != c9 & c0 != c10 & c0 != c11 & c0 != c12 & c0 != c13 &
  c0 != c14 & c0 != c15 & c0 != c16 &
  c1 != c2 & c1 != c3 & c1 != c4 & c1 != c5 & c1 != c6 & c1 != c7 &
  c1 != c8 & c1 != c9 & c1 != c10 & c1 != c11 & c1 != c12 & c1 != c13 &
  c1 != c14 & c1 != c15 & c1 != c16 &
  c2 != c3 & c2 != c4 & c2 != c5 & c2 != c6 & c2 != c7 &
  c2 != c8 & c2 != c9 & c2 != c10 & c2 != c11 & c2 != c12 & c2 != c13 &
  c2 != c14 & c2 != c15 & c2 != c16 &
  c3 != c4 & c3 != c5 & c3 != c6 & c3 != c7 &
  c3 != c8 & c3 != c9 & c3 != c10 & c3 != c11 & c3 != c12 & c3 != c13 &
  c3 != c14 & c3 != c15 & c3 != c16 &
  c4 != c5 & c4 != c6 & c4 != c7 &
  c4 != c8 & c4 != c9 & c4 != c10 & c4 != c11 & c4 != c12 & c4 != c13 &
  c4 != c14 & c4 != c15 & c4 != c16 &
  c5 != c6 & c5 != c7 &
  c5 != c8 & c5 != c9 & c5 != c10 & c5 != c11 & c5 != c12 & c5 != c13 &
  c5 != c14 & c5 != c15 & c5 != c16 &
  c6 != c7 &
  c6 != c8 & c6 != c9 & c6 != c10 & c6 != c11 & c6 != c12 & c6 != c13 &
  c6 != c14 & c6 != c15 & c6 != c16 &
  c7 != c8 & c7 != c9 & c7 != c10 & c7 != c11 & c7 != c12 & c7 != c13 &
  c7 != c14 & c7 != c15 & c7 != c16 &
  c8 != c9 & c8 != c10 & c8 != c11 & c8 != c12 & c8 != c13 &
  c8 != c14 & c8 != c15 & c8 != c16 &
  c9 != c10 & c9 != c11 & c9 != c12 & c9 != c13 &
  c9 != c14 & c9 != c15 & c9 != c16 &
  c10 != c11 & c10 != c12 & c10 != c13 &
  c10 != c14 & c10 != c15 & c10 != c16 &
  c11 != c12 & c11 != c13 &
  c11 != c14 & c11 != c15 & c11 != c16 &
  c12 != c13 &
  c12 != c14 & c12 != c15 & c12 != c16 &
  c13 != c14 & c13 != c15 & c13 != c16 &
  c14 != c15 & c14 != c16 &
  c15 != c16).

% Adj17 definition - all 68 directed edges
fof(adj17_def, axiom,
  ![X,Y]: (adj17(X,Y) <=> (
    (X = c0 & (Y = c9 | Y = c14 | Y = c15 | Y = c16)) |
    (X = c1 & (Y = c7 | Y = c11 | Y = c13 | Y = c16)) |
    (X = c2 & (Y = c8 | Y = c10 | Y = c12 | Y = c15)) |
    (X = c3 & (Y = c6 | Y = c8 | Y = c13 | Y = c15 | Y = c16)) |
    (X = c4 & (Y = c5 | Y = c7 | Y = c12 | Y = c14 | Y = c16)) |
    (X = c5 & (Y = c4 | Y = c9 | Y = c10 | Y = c11 | Y = c13)) |
    (X = c6 & (Y = c3 | Y = c10 | Y = c11 | Y = c12 | Y = c14)) |
    (X = c7 & (Y = c1 | Y = c4 | Y = c9 | Y = c10 | Y = c15)) |
    (X = c8 & (Y = c2 | Y = c3 | Y = c9 | Y = c11 | Y = c14)) |
    (X = c9 & (Y = c0 | Y = c5 | Y = c7 | Y = c8 | Y = c12)) |
    (X = c10 & (Y = c2 | Y = c5 | Y = c6 | Y = c7 | Y = c16)) |
    (X = c11 & (Y = c1 | Y = c5 | Y = c6 | Y = c8 | Y = c15)) |
    (X = c12 & (Y = c2 | Y = c4 | Y = c6 | Y = c9 | Y = c13)) |
    (X = c13 & (Y = c1 | Y = c3 | Y = c5 | Y = c12 | Y = c14)) |
    (X = c14 & (Y = c0 | Y = c4 | Y = c6 | Y = c8 | Y = c13)) |
    (X = c15 & (Y = c0 | Y = c2 | Y = c3 | Y = c7 | Y = c11)) |
    (X = c16 & (Y = c0 | Y = c1 | Y = c3 | Y = c4 | Y = c10))))).

% Conjecture: symmetry
fof(adj17_sym, conjecture, ![X,Y]: (adj17(X,Y) => adj17(Y,X))).
