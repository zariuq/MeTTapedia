% Extension Step v2: Tighter constraints
%
% Add the crucial constraint: if u1 is only adjacent to 'a' among {a,b,c,d},
% then {v0, u1, b, c, d} is a 5-indep set, and we need to extend THAT.
%
% This creates a recursive structure that eventually forces contradiction.

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% 5-indep set S = {v0, a, b, c, d}
fof(s_indep, axiom,
    ~adj(v0,a) & ~adj(v0,b) & ~adj(v0,c) & ~adj(v0,d) &
    ~adj(a,b) & ~adj(a,c) & ~adj(a,d) &
    ~adj(b,c) & ~adj(b,d) &
    ~adj(c,d)).

% U = {u1, u2, u3} are non-neighbors of v0 and pairwise non-adjacent (3-indep in U)
fof(u_not_adj_v0, axiom, ~adj(v0,u1) & ~adj(v0,u2) & ~adj(v0,u3)).
fof(u_indep, axiom, ~adj(u1,u2) & ~adj(u1,u3) & ~adj(u2,u3)).

% All distinct
fof(distinct_all, axiom,
    v0!=a & v0!=b & v0!=c & v0!=d & v0!=u1 & v0!=u2 & v0!=u3 &
    a!=b & a!=c & a!=d & a!=u1 & a!=u2 & a!=u3 &
    b!=c & b!=d & b!=u1 & b!=u2 & b!=u3 &
    c!=d & c!=u1 & c!=u2 & c!=u3 &
    d!=u1 & d!=u2 & d!=u3 &
    u1!=u2 & u1!=u3 &
    u2!=u3).

% Block u1 from {v0, a, b, c, d}: u1 must be adj to at least one of {a,b,c,d}
fof(block_u1, axiom, adj(u1,a) | adj(u1,b) | adj(u1,c) | adj(u1,d)).
fof(block_u2, axiom, adj(u2,a) | adj(u2,b) | adj(u2,c) | adj(u2,d)).
fof(block_u3, axiom, adj(u3,a) | adj(u3,b) | adj(u3,c) | adj(u3,d)).

% KEY: If u1 is NOT adjacent to {b,c,d}, then {v0, u1, b, c, d} is 5-indep.
% For that 5-indep to not extend to 6, u2 must be blocked from it.
% u2 is already non-adj to v0 and u1. So u2 must be adj to at least one of {b,c,d}.
%
% Similarly cascading constraints:

% If u1 avoids b,c,d (only hits a):
%   {v0, u1, b, c, d} is 5-indep
%   u2 must hit {b,c,d} to block, AND u3 must hit {b,c,d}
%   But {b,c,d} can only absorb so many edges...

% Encode: u1 must hit at least one of {b,c,d} OR u2,u3 must both hit {b,c,d}
% This is: ~(~adj(u1,b) & ~adj(u1,c) & ~adj(u1,d) &
%             (~adj(u2,b) | ~adj(u2,c) | ~adj(u2,d)) &
%             (~adj(u3,b) | ~adj(u3,c) | ~adj(u3,d)))

% Actually cleaner: if u1 avoids b,c,d, then for {v0,u1,b,c,d} 5-indep:
%   u2 must hit {b,c,d}: adj(u2,b) | adj(u2,c) | adj(u2,d)
%   u3 must hit {b,c,d}: adj(u3,b) | adj(u3,c) | adj(u3,d)
% So: (adj(u1,b) | adj(u1,c) | adj(u1,d)) |
%     ((adj(u2,b) | adj(u2,c) | adj(u2,d)) & (adj(u3,b) | adj(u3,c) | adj(u3,d)))

% Similarly with permutations. But this gets complex. Let me try a simpler encoding.

% Assume u1 only hits 'a' (and not b,c,d):
% Then block_u1 gives adj(u1,a)
% And the 5-indep {v0, u1, b, c, d} must be blocked.
% u2 is non-adj to v0, u1, so must hit {b,c,d}
% u3 is non-adj to v0, u1, so must hit {b,c,d}
% But u2 is also non-adj to u3. And if u2 only hits 'b', then {v0, u1, u2, c, d} is 5-indep!

% Let's trace this more carefully using explicit constraints.

% Case: u1 only hits a
% Then {v0, u1, b, c, d} is 5-indep.
% u2 blocks this iff u2 hits {b,c,d}.
%
% Subcase: u2 only hits b (among {b,c,d})
% Then {v0, u1, u2, c, d} is 5-indep.
% u3 blocks this iff u3 hits {c,d}.
%
% Subsubcase: u3 only hits c
% Then {v0, u1, u2, u3, d} is 5-indep!
% Now we need a 6th vertex non-adjacent to all of these.
% But {v0, u1, u2, u3, d} are 5 vertices from our 8.
% The remaining 3 (from the original U \ {u1,u2,u3}) must all be blocked.
% Each has degree ≤ 5...

% This analysis shows the constraints cascade. Let me just encode the full no-6-indep constraint.

% NO 6-independent set among {v0, a, b, c, d, u1, u2, u3}
fof(no_6_v0abcu1u2, axiom, adj(v0,a) | adj(v0,b) | adj(v0,c) | adj(v0,u1) | adj(v0,u2) |
                           adj(a,b) | adj(a,c) | adj(a,u1) | adj(a,u2) |
                           adj(b,c) | adj(b,u1) | adj(b,u2) |
                           adj(c,u1) | adj(c,u2) |
                           adj(u1,u2)).

fof(no_6_v0abdu1u2, axiom, adj(v0,a) | adj(v0,b) | adj(v0,d) | adj(v0,u1) | adj(v0,u2) |
                           adj(a,b) | adj(a,d) | adj(a,u1) | adj(a,u2) |
                           adj(b,d) | adj(b,u1) | adj(b,u2) |
                           adj(d,u1) | adj(d,u2) |
                           adj(u1,u2)).

fof(no_6_v0acdu1u2, axiom, adj(v0,a) | adj(v0,c) | adj(v0,d) | adj(v0,u1) | adj(v0,u2) |
                           adj(a,c) | adj(a,d) | adj(a,u1) | adj(a,u2) |
                           adj(c,d) | adj(c,u1) | adj(c,u2) |
                           adj(d,u1) | adj(d,u2) |
                           adj(u1,u2)).

fof(no_6_v0bcdu1u2, axiom, adj(v0,b) | adj(v0,c) | adj(v0,d) | adj(v0,u1) | adj(v0,u2) |
                           adj(b,c) | adj(b,d) | adj(b,u1) | adj(b,u2) |
                           adj(c,d) | adj(c,u1) | adj(c,u2) |
                           adj(d,u1) | adj(d,u2) |
                           adj(u1,u2)).

% Add more combinations involving u3
fof(no_6_v0abcu1u3, axiom, adj(v0,a) | adj(v0,b) | adj(v0,c) | adj(v0,u1) | adj(v0,u3) |
                           adj(a,b) | adj(a,c) | adj(a,u1) | adj(a,u3) |
                           adj(b,c) | adj(b,u1) | adj(b,u3) |
                           adj(c,u1) | adj(c,u3) |
                           adj(u1,u3)).

fof(no_6_v0abcu2u3, axiom, adj(v0,a) | adj(v0,b) | adj(v0,c) | adj(v0,u2) | adj(v0,u3) |
                           adj(a,b) | adj(a,c) | adj(a,u2) | adj(a,u3) |
                           adj(b,c) | adj(b,u2) | adj(b,u3) |
                           adj(c,u2) | adj(c,u3) |
                           adj(u2,u3)).

fof(no_6_v0abdu1u3, axiom, adj(v0,a) | adj(v0,b) | adj(v0,d) | adj(v0,u1) | adj(v0,u3) |
                           adj(a,b) | adj(a,d) | adj(a,u1) | adj(a,u3) |
                           adj(b,d) | adj(b,u1) | adj(b,u3) |
                           adj(d,u1) | adj(d,u3) |
                           adj(u1,u3)).

fof(no_6_v0abdu2u3, axiom, adj(v0,a) | adj(v0,b) | adj(v0,d) | adj(v0,u2) | adj(v0,u3) |
                           adj(a,b) | adj(a,d) | adj(a,u2) | adj(a,u3) |
                           adj(b,d) | adj(b,u2) | adj(b,u3) |
                           adj(d,u2) | adj(d,u3) |
                           adj(u2,u3)).

fof(no_6_v0acdu1u3, axiom, adj(v0,a) | adj(v0,c) | adj(v0,d) | adj(v0,u1) | adj(v0,u3) |
                           adj(a,c) | adj(a,d) | adj(a,u1) | adj(a,u3) |
                           adj(c,d) | adj(c,u1) | adj(c,u3) |
                           adj(d,u1) | adj(d,u3) |
                           adj(u1,u3)).

fof(no_6_v0acdu2u3, axiom, adj(v0,a) | adj(v0,c) | adj(v0,d) | adj(v0,u2) | adj(v0,u3) |
                           adj(a,c) | adj(a,d) | adj(a,u2) | adj(a,u3) |
                           adj(c,d) | adj(c,u2) | adj(c,u3) |
                           adj(d,u2) | adj(d,u3) |
                           adj(u2,u3)).

fof(no_6_v0bcdu1u3, axiom, adj(v0,b) | adj(v0,c) | adj(v0,d) | adj(v0,u1) | adj(v0,u3) |
                           adj(b,c) | adj(b,d) | adj(b,u1) | adj(b,u3) |
                           adj(c,d) | adj(c,u1) | adj(c,u3) |
                           adj(d,u1) | adj(d,u3) |
                           adj(u1,u3)).

fof(no_6_v0bcdu2u3, axiom, adj(v0,b) | adj(v0,c) | adj(v0,d) | adj(v0,u2) | adj(v0,u3) |
                           adj(b,c) | adj(b,d) | adj(b,u2) | adj(b,u3) |
                           adj(c,d) | adj(c,u2) | adj(c,u3) |
                           adj(d,u2) | adj(d,u3) |
                           adj(u2,u3)).

% Add the triple u combinations
fof(no_6_v0abu1u2u3, axiom, adj(v0,a) | adj(v0,b) | adj(v0,u1) | adj(v0,u2) | adj(v0,u3) |
                            adj(a,b) | adj(a,u1) | adj(a,u2) | adj(a,u3) |
                            adj(b,u1) | adj(b,u2) | adj(b,u3) |
                            adj(u1,u2) | adj(u1,u3) |
                            adj(u2,u3)).

fof(no_6_v0acu1u2u3, axiom, adj(v0,a) | adj(v0,c) | adj(v0,u1) | adj(v0,u2) | adj(v0,u3) |
                            adj(a,c) | adj(a,u1) | adj(a,u2) | adj(a,u3) |
                            adj(c,u1) | adj(c,u2) | adj(c,u3) |
                            adj(u1,u2) | adj(u1,u3) |
                            adj(u2,u3)).

fof(no_6_v0adu1u2u3, axiom, adj(v0,a) | adj(v0,d) | adj(v0,u1) | adj(v0,u2) | adj(v0,u3) |
                            adj(a,d) | adj(a,u1) | adj(a,u2) | adj(a,u3) |
                            adj(d,u1) | adj(d,u2) | adj(d,u3) |
                            adj(u1,u2) | adj(u1,u3) |
                            adj(u2,u3)).

fof(no_6_v0bcu1u2u3, axiom, adj(v0,b) | adj(v0,c) | adj(v0,u1) | adj(v0,u2) | adj(v0,u3) |
                            adj(b,c) | adj(b,u1) | adj(b,u2) | adj(b,u3) |
                            adj(c,u1) | adj(c,u2) | adj(c,u3) |
                            adj(u1,u2) | adj(u1,u3) |
                            adj(u2,u3)).

fof(no_6_v0bdu1u2u3, axiom, adj(v0,b) | adj(v0,d) | adj(v0,u1) | adj(v0,u2) | adj(v0,u3) |
                            adj(b,d) | adj(b,u1) | adj(b,u2) | adj(b,u3) |
                            adj(d,u1) | adj(d,u2) | adj(d,u3) |
                            adj(u1,u2) | adj(u1,u3) |
                            adj(u2,u3)).

fof(no_6_v0cdu1u2u3, axiom, adj(v0,c) | adj(v0,d) | adj(v0,u1) | adj(v0,u2) | adj(v0,u3) |
                            adj(c,d) | adj(c,u1) | adj(c,u2) | adj(c,u3) |
                            adj(d,u1) | adj(d,u2) | adj(d,u3) |
                            adj(u1,u2) | adj(u1,u3) |
                            adj(u2,u3)).

% 6-tuple with 4 from U (but we only have 3 u's, so skip)
% 6-tuple with all from {a,b,c,d,u1,u2,u3} minus v0 needs 6 = covered above

% Goal: contradiction
fof(goal, conjecture, $false).
