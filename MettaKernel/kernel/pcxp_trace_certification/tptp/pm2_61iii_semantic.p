% set.mm revision: 47e6e06b87581cd630d210dc41cf83b02eea78ea
% set.mm SHA-256: 3aecffcfcab6f6e114cce1d873a8300d7f41f24928648c04164aaa305b1f491a
% semantic entailment target: pm2.61iii (index 182)
% This tests intrinsic propositional difficulty, not Hilbert proof search.
fof(hypothesis_1, axiom, (~ (p_ph_182) => (~ (p_ps_182) => (~ (p_ch_182) => p_th_182)))).
fof(hypothesis_2, axiom, (p_ph_182 => p_th_182)).
fof(hypothesis_3, axiom, (p_ps_182 => p_th_182)).
fof(hypothesis_4, axiom, (p_ch_182 => p_th_182)).
fof(target, conjecture, p_th_182).
