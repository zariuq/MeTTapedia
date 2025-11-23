% TPTP: Degree parity contradiction on 9 vertices (propositional/SAT-friendly)
%
% We use edge propositions e_ij for i < j.
% Key insight: In 9-vertex triangle-free graph with no 4-indep set,
% every vertex must have degree exactly 3.
% But 9 * 3 = 27 is odd, contradicting handshake lemma.

% Edge predicates (symmetric)
fof(sym_01, axiom, adj(v0,v1) <=> adj(v1,v0)).
fof(sym_02, axiom, adj(v0,v2) <=> adj(v2,v0)).
fof(sym_03, axiom, adj(v0,v3) <=> adj(v3,v0)).
fof(sym_04, axiom, adj(v0,v4) <=> adj(v4,v0)).
fof(sym_05, axiom, adj(v0,v5) <=> adj(v5,v0)).
fof(sym_06, axiom, adj(v0,v6) <=> adj(v6,v0)).
fof(sym_07, axiom, adj(v0,v7) <=> adj(v7,v0)).
fof(sym_08, axiom, adj(v0,v8) <=> adj(v8,v0)).
fof(sym_12, axiom, adj(v1,v2) <=> adj(v2,v1)).
fof(sym_13, axiom, adj(v1,v3) <=> adj(v3,v1)).
fof(sym_14, axiom, adj(v1,v4) <=> adj(v4,v1)).
fof(sym_15, axiom, adj(v1,v5) <=> adj(v5,v1)).
fof(sym_16, axiom, adj(v1,v6) <=> adj(v6,v1)).
fof(sym_17, axiom, adj(v1,v7) <=> adj(v7,v1)).
fof(sym_18, axiom, adj(v1,v8) <=> adj(v8,v1)).
fof(sym_23, axiom, adj(v2,v3) <=> adj(v3,v2)).
fof(sym_24, axiom, adj(v2,v4) <=> adj(v4,v2)).
fof(sym_25, axiom, adj(v2,v5) <=> adj(v5,v2)).
fof(sym_26, axiom, adj(v2,v6) <=> adj(v6,v2)).
fof(sym_27, axiom, adj(v2,v7) <=> adj(v7,v2)).
fof(sym_28, axiom, adj(v2,v8) <=> adj(v8,v2)).
fof(sym_34, axiom, adj(v3,v4) <=> adj(v4,v3)).
fof(sym_35, axiom, adj(v3,v5) <=> adj(v5,v3)).
fof(sym_36, axiom, adj(v3,v6) <=> adj(v6,v3)).
fof(sym_37, axiom, adj(v3,v7) <=> adj(v7,v3)).
fof(sym_38, axiom, adj(v3,v8) <=> adj(v8,v3)).
fof(sym_45, axiom, adj(v4,v5) <=> adj(v5,v4)).
fof(sym_46, axiom, adj(v4,v6) <=> adj(v6,v4)).
fof(sym_47, axiom, adj(v4,v7) <=> adj(v7,v4)).
fof(sym_48, axiom, adj(v4,v8) <=> adj(v8,v4)).
fof(sym_56, axiom, adj(v5,v6) <=> adj(v6,v5)).
fof(sym_57, axiom, adj(v5,v7) <=> adj(v7,v5)).
fof(sym_58, axiom, adj(v5,v8) <=> adj(v8,v5)).
fof(sym_67, axiom, adj(v6,v7) <=> adj(v7,v6)).
fof(sym_68, axiom, adj(v6,v8) <=> adj(v8,v6)).
fof(sym_78, axiom, adj(v7,v8) <=> adj(v8,v7)).

% No self-loops
fof(irref0, axiom, ~adj(v0,v0)).
fof(irref1, axiom, ~adj(v1,v1)).
fof(irref2, axiom, ~adj(v2,v2)).
fof(irref3, axiom, ~adj(v3,v3)).
fof(irref4, axiom, ~adj(v4,v4)).
fof(irref5, axiom, ~adj(v5,v5)).
fof(irref6, axiom, ~adj(v6,v6)).
fof(irref7, axiom, ~adj(v7,v7)).
fof(irref8, axiom, ~adj(v8,v8)).

% All C(9,3) = 84 triangle-free constraints
fof(tf_012, axiom, ~(adj(v0,v1) & adj(v1,v2) & adj(v0,v2))).
fof(tf_013, axiom, ~(adj(v0,v1) & adj(v1,v3) & adj(v0,v3))).
fof(tf_014, axiom, ~(adj(v0,v1) & adj(v1,v4) & adj(v0,v4))).
fof(tf_015, axiom, ~(adj(v0,v1) & adj(v1,v5) & adj(v0,v5))).
fof(tf_016, axiom, ~(adj(v0,v1) & adj(v1,v6) & adj(v0,v6))).
fof(tf_017, axiom, ~(adj(v0,v1) & adj(v1,v7) & adj(v0,v7))).
fof(tf_018, axiom, ~(adj(v0,v1) & adj(v1,v8) & adj(v0,v8))).
fof(tf_023, axiom, ~(adj(v0,v2) & adj(v2,v3) & adj(v0,v3))).
fof(tf_024, axiom, ~(adj(v0,v2) & adj(v2,v4) & adj(v0,v4))).
fof(tf_025, axiom, ~(adj(v0,v2) & adj(v2,v5) & adj(v0,v5))).
fof(tf_026, axiom, ~(adj(v0,v2) & adj(v2,v6) & adj(v0,v6))).
fof(tf_027, axiom, ~(adj(v0,v2) & adj(v2,v7) & adj(v0,v7))).
fof(tf_028, axiom, ~(adj(v0,v2) & adj(v2,v8) & adj(v0,v8))).
fof(tf_034, axiom, ~(adj(v0,v3) & adj(v3,v4) & adj(v0,v4))).
fof(tf_035, axiom, ~(adj(v0,v3) & adj(v3,v5) & adj(v0,v5))).
fof(tf_036, axiom, ~(adj(v0,v3) & adj(v3,v6) & adj(v0,v6))).
fof(tf_037, axiom, ~(adj(v0,v3) & adj(v3,v7) & adj(v0,v7))).
fof(tf_038, axiom, ~(adj(v0,v3) & adj(v3,v8) & adj(v0,v8))).
fof(tf_045, axiom, ~(adj(v0,v4) & adj(v4,v5) & adj(v0,v5))).
fof(tf_046, axiom, ~(adj(v0,v4) & adj(v4,v6) & adj(v0,v6))).
fof(tf_047, axiom, ~(adj(v0,v4) & adj(v4,v7) & adj(v0,v7))).
fof(tf_048, axiom, ~(adj(v0,v4) & adj(v4,v8) & adj(v0,v8))).
fof(tf_056, axiom, ~(adj(v0,v5) & adj(v5,v6) & adj(v0,v6))).
fof(tf_057, axiom, ~(adj(v0,v5) & adj(v5,v7) & adj(v0,v7))).
fof(tf_058, axiom, ~(adj(v0,v5) & adj(v5,v8) & adj(v0,v8))).
fof(tf_067, axiom, ~(adj(v0,v6) & adj(v6,v7) & adj(v0,v7))).
fof(tf_068, axiom, ~(adj(v0,v6) & adj(v6,v8) & adj(v0,v8))).
fof(tf_078, axiom, ~(adj(v0,v7) & adj(v7,v8) & adj(v0,v8))).
fof(tf_123, axiom, ~(adj(v1,v2) & adj(v2,v3) & adj(v1,v3))).
fof(tf_124, axiom, ~(adj(v1,v2) & adj(v2,v4) & adj(v1,v4))).
fof(tf_125, axiom, ~(adj(v1,v2) & adj(v2,v5) & adj(v1,v5))).
fof(tf_126, axiom, ~(adj(v1,v2) & adj(v2,v6) & adj(v1,v6))).
fof(tf_127, axiom, ~(adj(v1,v2) & adj(v2,v7) & adj(v1,v7))).
fof(tf_128, axiom, ~(adj(v1,v2) & adj(v2,v8) & adj(v1,v8))).
fof(tf_134, axiom, ~(adj(v1,v3) & adj(v3,v4) & adj(v1,v4))).
fof(tf_135, axiom, ~(adj(v1,v3) & adj(v3,v5) & adj(v1,v5))).
fof(tf_136, axiom, ~(adj(v1,v3) & adj(v3,v6) & adj(v1,v6))).
fof(tf_137, axiom, ~(adj(v1,v3) & adj(v3,v7) & adj(v1,v7))).
fof(tf_138, axiom, ~(adj(v1,v3) & adj(v3,v8) & adj(v1,v8))).
fof(tf_145, axiom, ~(adj(v1,v4) & adj(v4,v5) & adj(v1,v5))).
fof(tf_146, axiom, ~(adj(v1,v4) & adj(v4,v6) & adj(v1,v6))).
fof(tf_147, axiom, ~(adj(v1,v4) & adj(v4,v7) & adj(v1,v7))).
fof(tf_148, axiom, ~(adj(v1,v4) & adj(v4,v8) & adj(v1,v8))).
fof(tf_156, axiom, ~(adj(v1,v5) & adj(v5,v6) & adj(v1,v6))).
fof(tf_157, axiom, ~(adj(v1,v5) & adj(v5,v7) & adj(v1,v7))).
fof(tf_158, axiom, ~(adj(v1,v5) & adj(v5,v8) & adj(v1,v8))).
fof(tf_167, axiom, ~(adj(v1,v6) & adj(v6,v7) & adj(v1,v7))).
fof(tf_168, axiom, ~(adj(v1,v6) & adj(v6,v8) & adj(v1,v8))).
fof(tf_178, axiom, ~(adj(v1,v7) & adj(v7,v8) & adj(v1,v8))).
fof(tf_234, axiom, ~(adj(v2,v3) & adj(v3,v4) & adj(v2,v4))).
fof(tf_235, axiom, ~(adj(v2,v3) & adj(v3,v5) & adj(v2,v5))).
fof(tf_236, axiom, ~(adj(v2,v3) & adj(v3,v6) & adj(v2,v6))).
fof(tf_237, axiom, ~(adj(v2,v3) & adj(v3,v7) & adj(v2,v7))).
fof(tf_238, axiom, ~(adj(v2,v3) & adj(v3,v8) & adj(v2,v8))).
fof(tf_245, axiom, ~(adj(v2,v4) & adj(v4,v5) & adj(v2,v5))).
fof(tf_246, axiom, ~(adj(v2,v4) & adj(v4,v6) & adj(v2,v6))).
fof(tf_247, axiom, ~(adj(v2,v4) & adj(v4,v7) & adj(v2,v7))).
fof(tf_248, axiom, ~(adj(v2,v4) & adj(v4,v8) & adj(v2,v8))).
fof(tf_256, axiom, ~(adj(v2,v5) & adj(v5,v6) & adj(v2,v6))).
fof(tf_257, axiom, ~(adj(v2,v5) & adj(v5,v7) & adj(v2,v7))).
fof(tf_258, axiom, ~(adj(v2,v5) & adj(v5,v8) & adj(v2,v8))).
fof(tf_267, axiom, ~(adj(v2,v6) & adj(v6,v7) & adj(v2,v7))).
fof(tf_268, axiom, ~(adj(v2,v6) & adj(v6,v8) & adj(v2,v8))).
fof(tf_278, axiom, ~(adj(v2,v7) & adj(v7,v8) & adj(v2,v8))).
fof(tf_345, axiom, ~(adj(v3,v4) & adj(v4,v5) & adj(v3,v5))).
fof(tf_346, axiom, ~(adj(v3,v4) & adj(v4,v6) & adj(v3,v6))).
fof(tf_347, axiom, ~(adj(v3,v4) & adj(v4,v7) & adj(v3,v7))).
fof(tf_348, axiom, ~(adj(v3,v4) & adj(v4,v8) & adj(v3,v8))).
fof(tf_356, axiom, ~(adj(v3,v5) & adj(v5,v6) & adj(v3,v6))).
fof(tf_357, axiom, ~(adj(v3,v5) & adj(v5,v7) & adj(v3,v7))).
fof(tf_358, axiom, ~(adj(v3,v5) & adj(v5,v8) & adj(v3,v8))).
fof(tf_367, axiom, ~(adj(v3,v6) & adj(v6,v7) & adj(v3,v7))).
fof(tf_368, axiom, ~(adj(v3,v6) & adj(v6,v8) & adj(v3,v8))).
fof(tf_378, axiom, ~(adj(v3,v7) & adj(v7,v8) & adj(v3,v8))).
fof(tf_456, axiom, ~(adj(v4,v5) & adj(v5,v6) & adj(v4,v6))).
fof(tf_457, axiom, ~(adj(v4,v5) & adj(v5,v7) & adj(v4,v7))).
fof(tf_458, axiom, ~(adj(v4,v5) & adj(v5,v8) & adj(v4,v8))).
fof(tf_467, axiom, ~(adj(v4,v6) & adj(v6,v7) & adj(v4,v7))).
fof(tf_468, axiom, ~(adj(v4,v6) & adj(v6,v8) & adj(v4,v8))).
fof(tf_478, axiom, ~(adj(v4,v7) & adj(v7,v8) & adj(v4,v8))).
fof(tf_567, axiom, ~(adj(v5,v6) & adj(v6,v7) & adj(v5,v7))).
fof(tf_568, axiom, ~(adj(v5,v6) & adj(v6,v8) & adj(v5,v8))).
fof(tf_578, axiom, ~(adj(v5,v7) & adj(v7,v8) & adj(v5,v8))).
fof(tf_678, axiom, ~(adj(v6,v7) & adj(v7,v8) & adj(v6,v8))).

% All C(9,4) = 126 no-4-independent constraints
fof(i4_0123, axiom, adj(v0,v1) | adj(v0,v2) | adj(v0,v3) | adj(v1,v2) | adj(v1,v3) | adj(v2,v3)).
fof(i4_0124, axiom, adj(v0,v1) | adj(v0,v2) | adj(v0,v4) | adj(v1,v2) | adj(v1,v4) | adj(v2,v4)).
fof(i4_0125, axiom, adj(v0,v1) | adj(v0,v2) | adj(v0,v5) | adj(v1,v2) | adj(v1,v5) | adj(v2,v5)).
fof(i4_0126, axiom, adj(v0,v1) | adj(v0,v2) | adj(v0,v6) | adj(v1,v2) | adj(v1,v6) | adj(v2,v6)).
fof(i4_0127, axiom, adj(v0,v1) | adj(v0,v2) | adj(v0,v7) | adj(v1,v2) | adj(v1,v7) | adj(v2,v7)).
fof(i4_0128, axiom, adj(v0,v1) | adj(v0,v2) | adj(v0,v8) | adj(v1,v2) | adj(v1,v8) | adj(v2,v8)).
fof(i4_0134, axiom, adj(v0,v1) | adj(v0,v3) | adj(v0,v4) | adj(v1,v3) | adj(v1,v4) | adj(v3,v4)).
fof(i4_0135, axiom, adj(v0,v1) | adj(v0,v3) | adj(v0,v5) | adj(v1,v3) | adj(v1,v5) | adj(v3,v5)).
fof(i4_0136, axiom, adj(v0,v1) | adj(v0,v3) | adj(v0,v6) | adj(v1,v3) | adj(v1,v6) | adj(v3,v6)).
fof(i4_0137, axiom, adj(v0,v1) | adj(v0,v3) | adj(v0,v7) | adj(v1,v3) | adj(v1,v7) | adj(v3,v7)).
fof(i4_0138, axiom, adj(v0,v1) | adj(v0,v3) | adj(v0,v8) | adj(v1,v3) | adj(v1,v8) | adj(v3,v8)).
fof(i4_0145, axiom, adj(v0,v1) | adj(v0,v4) | adj(v0,v5) | adj(v1,v4) | adj(v1,v5) | adj(v4,v5)).
fof(i4_0146, axiom, adj(v0,v1) | adj(v0,v4) | adj(v0,v6) | adj(v1,v4) | adj(v1,v6) | adj(v4,v6)).
fof(i4_0147, axiom, adj(v0,v1) | adj(v0,v4) | adj(v0,v7) | adj(v1,v4) | adj(v1,v7) | adj(v4,v7)).
fof(i4_0148, axiom, adj(v0,v1) | adj(v0,v4) | adj(v0,v8) | adj(v1,v4) | adj(v1,v8) | adj(v4,v8)).
fof(i4_0156, axiom, adj(v0,v1) | adj(v0,v5) | adj(v0,v6) | adj(v1,v5) | adj(v1,v6) | adj(v5,v6)).
fof(i4_0157, axiom, adj(v0,v1) | adj(v0,v5) | adj(v0,v7) | adj(v1,v5) | adj(v1,v7) | adj(v5,v7)).
fof(i4_0158, axiom, adj(v0,v1) | adj(v0,v5) | adj(v0,v8) | adj(v1,v5) | adj(v1,v8) | adj(v5,v8)).
fof(i4_0167, axiom, adj(v0,v1) | adj(v0,v6) | adj(v0,v7) | adj(v1,v6) | adj(v1,v7) | adj(v6,v7)).
fof(i4_0168, axiom, adj(v0,v1) | adj(v0,v6) | adj(v0,v8) | adj(v1,v6) | adj(v1,v8) | adj(v6,v8)).
fof(i4_0178, axiom, adj(v0,v1) | adj(v0,v7) | adj(v0,v8) | adj(v1,v7) | adj(v1,v8) | adj(v7,v8)).
fof(i4_0234, axiom, adj(v0,v2) | adj(v0,v3) | adj(v0,v4) | adj(v2,v3) | adj(v2,v4) | adj(v3,v4)).
fof(i4_0235, axiom, adj(v0,v2) | adj(v0,v3) | adj(v0,v5) | adj(v2,v3) | adj(v2,v5) | adj(v3,v5)).
fof(i4_0236, axiom, adj(v0,v2) | adj(v0,v3) | adj(v0,v6) | adj(v2,v3) | adj(v2,v6) | adj(v3,v6)).
fof(i4_0237, axiom, adj(v0,v2) | adj(v0,v3) | adj(v0,v7) | adj(v2,v3) | adj(v2,v7) | adj(v3,v7)).
fof(i4_0238, axiom, adj(v0,v2) | adj(v0,v3) | adj(v0,v8) | adj(v2,v3) | adj(v2,v8) | adj(v3,v8)).
fof(i4_0245, axiom, adj(v0,v2) | adj(v0,v4) | adj(v0,v5) | adj(v2,v4) | adj(v2,v5) | adj(v4,v5)).
fof(i4_0246, axiom, adj(v0,v2) | adj(v0,v4) | adj(v0,v6) | adj(v2,v4) | adj(v2,v6) | adj(v4,v6)).
fof(i4_0247, axiom, adj(v0,v2) | adj(v0,v4) | adj(v0,v7) | adj(v2,v4) | adj(v2,v7) | adj(v4,v7)).
fof(i4_0248, axiom, adj(v0,v2) | adj(v0,v4) | adj(v0,v8) | adj(v2,v4) | adj(v2,v8) | adj(v4,v8)).
fof(i4_0256, axiom, adj(v0,v2) | adj(v0,v5) | adj(v0,v6) | adj(v2,v5) | adj(v2,v6) | adj(v5,v6)).
fof(i4_0257, axiom, adj(v0,v2) | adj(v0,v5) | adj(v0,v7) | adj(v2,v5) | adj(v2,v7) | adj(v5,v7)).
fof(i4_0258, axiom, adj(v0,v2) | adj(v0,v5) | adj(v0,v8) | adj(v2,v5) | adj(v2,v8) | adj(v5,v8)).
fof(i4_0267, axiom, adj(v0,v2) | adj(v0,v6) | adj(v0,v7) | adj(v2,v6) | adj(v2,v7) | adj(v6,v7)).
fof(i4_0268, axiom, adj(v0,v2) | adj(v0,v6) | adj(v0,v8) | adj(v2,v6) | adj(v2,v8) | adj(v6,v8)).
fof(i4_0278, axiom, adj(v0,v2) | adj(v0,v7) | adj(v0,v8) | adj(v2,v7) | adj(v2,v8) | adj(v7,v8)).
fof(i4_0345, axiom, adj(v0,v3) | adj(v0,v4) | adj(v0,v5) | adj(v3,v4) | adj(v3,v5) | adj(v4,v5)).
fof(i4_0346, axiom, adj(v0,v3) | adj(v0,v4) | adj(v0,v6) | adj(v3,v4) | adj(v3,v6) | adj(v4,v6)).
fof(i4_0347, axiom, adj(v0,v3) | adj(v0,v4) | adj(v0,v7) | adj(v3,v4) | adj(v3,v7) | adj(v4,v7)).
fof(i4_0348, axiom, adj(v0,v3) | adj(v0,v4) | adj(v0,v8) | adj(v3,v4) | adj(v3,v8) | adj(v4,v8)).
fof(i4_0356, axiom, adj(v0,v3) | adj(v0,v5) | adj(v0,v6) | adj(v3,v5) | adj(v3,v6) | adj(v5,v6)).
fof(i4_0357, axiom, adj(v0,v3) | adj(v0,v5) | adj(v0,v7) | adj(v3,v5) | adj(v3,v7) | adj(v5,v7)).
fof(i4_0358, axiom, adj(v0,v3) | adj(v0,v5) | adj(v0,v8) | adj(v3,v5) | adj(v3,v8) | adj(v5,v8)).
fof(i4_0367, axiom, adj(v0,v3) | adj(v0,v6) | adj(v0,v7) | adj(v3,v6) | adj(v3,v7) | adj(v6,v7)).
fof(i4_0368, axiom, adj(v0,v3) | adj(v0,v6) | adj(v0,v8) | adj(v3,v6) | adj(v3,v8) | adj(v6,v8)).
fof(i4_0378, axiom, adj(v0,v3) | adj(v0,v7) | adj(v0,v8) | adj(v3,v7) | adj(v3,v8) | adj(v7,v8)).
fof(i4_0456, axiom, adj(v0,v4) | adj(v0,v5) | adj(v0,v6) | adj(v4,v5) | adj(v4,v6) | adj(v5,v6)).
fof(i4_0457, axiom, adj(v0,v4) | adj(v0,v5) | adj(v0,v7) | adj(v4,v5) | adj(v4,v7) | adj(v5,v7)).
fof(i4_0458, axiom, adj(v0,v4) | adj(v0,v5) | adj(v0,v8) | adj(v4,v5) | adj(v4,v8) | adj(v5,v8)).
fof(i4_0467, axiom, adj(v0,v4) | adj(v0,v6) | adj(v0,v7) | adj(v4,v6) | adj(v4,v7) | adj(v6,v7)).
fof(i4_0468, axiom, adj(v0,v4) | adj(v0,v6) | adj(v0,v8) | adj(v4,v6) | adj(v4,v8) | adj(v6,v8)).
fof(i4_0478, axiom, adj(v0,v4) | adj(v0,v7) | adj(v0,v8) | adj(v4,v7) | adj(v4,v8) | adj(v7,v8)).
fof(i4_0567, axiom, adj(v0,v5) | adj(v0,v6) | adj(v0,v7) | adj(v5,v6) | adj(v5,v7) | adj(v6,v7)).
fof(i4_0568, axiom, adj(v0,v5) | adj(v0,v6) | adj(v0,v8) | adj(v5,v6) | adj(v5,v8) | adj(v6,v8)).
fof(i4_0578, axiom, adj(v0,v5) | adj(v0,v7) | adj(v0,v8) | adj(v5,v7) | adj(v5,v8) | adj(v7,v8)).
fof(i4_0678, axiom, adj(v0,v6) | adj(v0,v7) | adj(v0,v8) | adj(v6,v7) | adj(v6,v8) | adj(v7,v8)).
fof(i4_1234, axiom, adj(v1,v2) | adj(v1,v3) | adj(v1,v4) | adj(v2,v3) | adj(v2,v4) | adj(v3,v4)).
fof(i4_1235, axiom, adj(v1,v2) | adj(v1,v3) | adj(v1,v5) | adj(v2,v3) | adj(v2,v5) | adj(v3,v5)).
fof(i4_1236, axiom, adj(v1,v2) | adj(v1,v3) | adj(v1,v6) | adj(v2,v3) | adj(v2,v6) | adj(v3,v6)).
fof(i4_1237, axiom, adj(v1,v2) | adj(v1,v3) | adj(v1,v7) | adj(v2,v3) | adj(v2,v7) | adj(v3,v7)).
fof(i4_1238, axiom, adj(v1,v2) | adj(v1,v3) | adj(v1,v8) | adj(v2,v3) | adj(v2,v8) | adj(v3,v8)).
fof(i4_1245, axiom, adj(v1,v2) | adj(v1,v4) | adj(v1,v5) | adj(v2,v4) | adj(v2,v5) | adj(v4,v5)).
fof(i4_1246, axiom, adj(v1,v2) | adj(v1,v4) | adj(v1,v6) | adj(v2,v4) | adj(v2,v6) | adj(v4,v6)).
fof(i4_1247, axiom, adj(v1,v2) | adj(v1,v4) | adj(v1,v7) | adj(v2,v4) | adj(v2,v7) | adj(v4,v7)).
fof(i4_1248, axiom, adj(v1,v2) | adj(v1,v4) | adj(v1,v8) | adj(v2,v4) | adj(v2,v8) | adj(v4,v8)).
fof(i4_1256, axiom, adj(v1,v2) | adj(v1,v5) | adj(v1,v6) | adj(v2,v5) | adj(v2,v6) | adj(v5,v6)).
fof(i4_1257, axiom, adj(v1,v2) | adj(v1,v5) | adj(v1,v7) | adj(v2,v5) | adj(v2,v7) | adj(v5,v7)).
fof(i4_1258, axiom, adj(v1,v2) | adj(v1,v5) | adj(v1,v8) | adj(v2,v5) | adj(v2,v8) | adj(v5,v8)).
fof(i4_1267, axiom, adj(v1,v2) | adj(v1,v6) | adj(v1,v7) | adj(v2,v6) | adj(v2,v7) | adj(v6,v7)).
fof(i4_1268, axiom, adj(v1,v2) | adj(v1,v6) | adj(v1,v8) | adj(v2,v6) | adj(v2,v8) | adj(v6,v8)).
fof(i4_1278, axiom, adj(v1,v2) | adj(v1,v7) | adj(v1,v8) | adj(v2,v7) | adj(v2,v8) | adj(v7,v8)).
fof(i4_1345, axiom, adj(v1,v3) | adj(v1,v4) | adj(v1,v5) | adj(v3,v4) | adj(v3,v5) | adj(v4,v5)).
fof(i4_1346, axiom, adj(v1,v3) | adj(v1,v4) | adj(v1,v6) | adj(v3,v4) | adj(v3,v6) | adj(v4,v6)).
fof(i4_1347, axiom, adj(v1,v3) | adj(v1,v4) | adj(v1,v7) | adj(v3,v4) | adj(v3,v7) | adj(v4,v7)).
fof(i4_1348, axiom, adj(v1,v3) | adj(v1,v4) | adj(v1,v8) | adj(v3,v4) | adj(v3,v8) | adj(v4,v8)).
fof(i4_1356, axiom, adj(v1,v3) | adj(v1,v5) | adj(v1,v6) | adj(v3,v5) | adj(v3,v6) | adj(v5,v6)).
fof(i4_1357, axiom, adj(v1,v3) | adj(v1,v5) | adj(v1,v7) | adj(v3,v5) | adj(v3,v7) | adj(v5,v7)).
fof(i4_1358, axiom, adj(v1,v3) | adj(v1,v5) | adj(v1,v8) | adj(v3,v5) | adj(v3,v8) | adj(v5,v8)).
fof(i4_1367, axiom, adj(v1,v3) | adj(v1,v6) | adj(v1,v7) | adj(v3,v6) | adj(v3,v7) | adj(v6,v7)).
fof(i4_1368, axiom, adj(v1,v3) | adj(v1,v6) | adj(v1,v8) | adj(v3,v6) | adj(v3,v8) | adj(v6,v8)).
fof(i4_1378, axiom, adj(v1,v3) | adj(v1,v7) | adj(v1,v8) | adj(v3,v7) | adj(v3,v8) | adj(v7,v8)).
fof(i4_1456, axiom, adj(v1,v4) | adj(v1,v5) | adj(v1,v6) | adj(v4,v5) | adj(v4,v6) | adj(v5,v6)).
fof(i4_1457, axiom, adj(v1,v4) | adj(v1,v5) | adj(v1,v7) | adj(v4,v5) | adj(v4,v7) | adj(v5,v7)).
fof(i4_1458, axiom, adj(v1,v4) | adj(v1,v5) | adj(v1,v8) | adj(v4,v5) | adj(v4,v8) | adj(v5,v8)).
fof(i4_1467, axiom, adj(v1,v4) | adj(v1,v6) | adj(v1,v7) | adj(v4,v6) | adj(v4,v7) | adj(v6,v7)).
fof(i4_1468, axiom, adj(v1,v4) | adj(v1,v6) | adj(v1,v8) | adj(v4,v6) | adj(v4,v8) | adj(v6,v8)).
fof(i4_1478, axiom, adj(v1,v4) | adj(v1,v7) | adj(v1,v8) | adj(v4,v7) | adj(v4,v8) | adj(v7,v8)).
fof(i4_1567, axiom, adj(v1,v5) | adj(v1,v6) | adj(v1,v7) | adj(v5,v6) | adj(v5,v7) | adj(v6,v7)).
fof(i4_1568, axiom, adj(v1,v5) | adj(v1,v6) | adj(v1,v8) | adj(v5,v6) | adj(v5,v8) | adj(v6,v8)).
fof(i4_1578, axiom, adj(v1,v5) | adj(v1,v7) | adj(v1,v8) | adj(v5,v7) | adj(v5,v8) | adj(v7,v8)).
fof(i4_1678, axiom, adj(v1,v6) | adj(v1,v7) | adj(v1,v8) | adj(v6,v7) | adj(v6,v8) | adj(v7,v8)).
fof(i4_2345, axiom, adj(v2,v3) | adj(v2,v4) | adj(v2,v5) | adj(v3,v4) | adj(v3,v5) | adj(v4,v5)).
fof(i4_2346, axiom, adj(v2,v3) | adj(v2,v4) | adj(v2,v6) | adj(v3,v4) | adj(v3,v6) | adj(v4,v6)).
fof(i4_2347, axiom, adj(v2,v3) | adj(v2,v4) | adj(v2,v7) | adj(v3,v4) | adj(v3,v7) | adj(v4,v7)).
fof(i4_2348, axiom, adj(v2,v3) | adj(v2,v4) | adj(v2,v8) | adj(v3,v4) | adj(v3,v8) | adj(v4,v8)).
fof(i4_2356, axiom, adj(v2,v3) | adj(v2,v5) | adj(v2,v6) | adj(v3,v5) | adj(v3,v6) | adj(v5,v6)).
fof(i4_2357, axiom, adj(v2,v3) | adj(v2,v5) | adj(v2,v7) | adj(v3,v5) | adj(v3,v7) | adj(v5,v7)).
fof(i4_2358, axiom, adj(v2,v3) | adj(v2,v5) | adj(v2,v8) | adj(v3,v5) | adj(v3,v8) | adj(v5,v8)).
fof(i4_2367, axiom, adj(v2,v3) | adj(v2,v6) | adj(v2,v7) | adj(v3,v6) | adj(v3,v7) | adj(v6,v7)).
fof(i4_2368, axiom, adj(v2,v3) | adj(v2,v6) | adj(v2,v8) | adj(v3,v6) | adj(v3,v8) | adj(v6,v8)).
fof(i4_2378, axiom, adj(v2,v3) | adj(v2,v7) | adj(v2,v8) | adj(v3,v7) | adj(v3,v8) | adj(v7,v8)).
fof(i4_2456, axiom, adj(v2,v4) | adj(v2,v5) | adj(v2,v6) | adj(v4,v5) | adj(v4,v6) | adj(v5,v6)).
fof(i4_2457, axiom, adj(v2,v4) | adj(v2,v5) | adj(v2,v7) | adj(v4,v5) | adj(v4,v7) | adj(v5,v7)).
fof(i4_2458, axiom, adj(v2,v4) | adj(v2,v5) | adj(v2,v8) | adj(v4,v5) | adj(v4,v8) | adj(v5,v8)).
fof(i4_2467, axiom, adj(v2,v4) | adj(v2,v6) | adj(v2,v7) | adj(v4,v6) | adj(v4,v7) | adj(v6,v7)).
fof(i4_2468, axiom, adj(v2,v4) | adj(v2,v6) | adj(v2,v8) | adj(v4,v6) | adj(v4,v8) | adj(v6,v8)).
fof(i4_2478, axiom, adj(v2,v4) | adj(v2,v7) | adj(v2,v8) | adj(v4,v7) | adj(v4,v8) | adj(v7,v8)).
fof(i4_2567, axiom, adj(v2,v5) | adj(v2,v6) | adj(v2,v7) | adj(v5,v6) | adj(v5,v7) | adj(v6,v7)).
fof(i4_2568, axiom, adj(v2,v5) | adj(v2,v6) | adj(v2,v8) | adj(v5,v6) | adj(v5,v8) | adj(v6,v8)).
fof(i4_2578, axiom, adj(v2,v5) | adj(v2,v7) | adj(v2,v8) | adj(v5,v7) | adj(v5,v8) | adj(v7,v8)).
fof(i4_2678, axiom, adj(v2,v6) | adj(v2,v7) | adj(v2,v8) | adj(v6,v7) | adj(v6,v8) | adj(v7,v8)).
fof(i4_3456, axiom, adj(v3,v4) | adj(v3,v5) | adj(v3,v6) | adj(v4,v5) | adj(v4,v6) | adj(v5,v6)).
fof(i4_3457, axiom, adj(v3,v4) | adj(v3,v5) | adj(v3,v7) | adj(v4,v5) | adj(v4,v7) | adj(v5,v7)).
fof(i4_3458, axiom, adj(v3,v4) | adj(v3,v5) | adj(v3,v8) | adj(v4,v5) | adj(v4,v8) | adj(v5,v8)).
fof(i4_3467, axiom, adj(v3,v4) | adj(v3,v6) | adj(v3,v7) | adj(v4,v6) | adj(v4,v7) | adj(v6,v7)).
fof(i4_3468, axiom, adj(v3,v4) | adj(v3,v6) | adj(v3,v8) | adj(v4,v6) | adj(v4,v8) | adj(v6,v8)).
fof(i4_3478, axiom, adj(v3,v4) | adj(v3,v7) | adj(v3,v8) | adj(v4,v7) | adj(v4,v8) | adj(v7,v8)).
fof(i4_3567, axiom, adj(v3,v5) | adj(v3,v6) | adj(v3,v7) | adj(v5,v6) | adj(v5,v7) | adj(v6,v7)).
fof(i4_3568, axiom, adj(v3,v5) | adj(v3,v6) | adj(v3,v8) | adj(v5,v6) | adj(v5,v8) | adj(v6,v8)).
fof(i4_3578, axiom, adj(v3,v5) | adj(v3,v7) | adj(v3,v8) | adj(v5,v7) | adj(v5,v8) | adj(v7,v8)).
fof(i4_3678, axiom, adj(v3,v6) | adj(v3,v7) | adj(v3,v8) | adj(v6,v7) | adj(v6,v8) | adj(v7,v8)).
fof(i4_4567, axiom, adj(v4,v5) | adj(v4,v6) | adj(v4,v7) | adj(v5,v6) | adj(v5,v7) | adj(v6,v7)).
fof(i4_4568, axiom, adj(v4,v5) | adj(v4,v6) | adj(v4,v8) | adj(v5,v6) | adj(v5,v8) | adj(v6,v8)).
fof(i4_4578, axiom, adj(v4,v5) | adj(v4,v7) | adj(v4,v8) | adj(v5,v7) | adj(v5,v8) | adj(v7,v8)).
fof(i4_4678, axiom, adj(v4,v6) | adj(v4,v7) | adj(v4,v8) | adj(v6,v7) | adj(v6,v8) | adj(v7,v8)).
fof(i4_5678, axiom, adj(v5,v6) | adj(v5,v7) | adj(v5,v8) | adj(v6,v7) | adj(v6,v8) | adj(v7,v8)).

% Goal: find a valid graph (SAT) or prove no such graph exists (UNSAT)
% The handshake lemma parity contradiction isn't directly encodable in FOL
% but the constraints themselves may already be UNSAT
fof(goal, conjecture, $false).
