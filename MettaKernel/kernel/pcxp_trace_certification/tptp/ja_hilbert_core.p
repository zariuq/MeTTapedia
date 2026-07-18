% set.mm revision: 47e6e06b87581cd630d210dc41cf83b02eea78ea
% set.mm SHA-256: 3aecffcfcab6f6e114cce1d873a8300d7f41f24928648c04164aaa305b1f491a
% target: ja (index 183)
% theory policy: core
% No target proof labels are inputs.
fof(rule_ax_mp, axiom, ! [V_PH, V_PS] : (((proved(V_PH) & proved(imp(V_PH,V_PS))) => proved(V_PS)))).
fof(rule_ax_1, axiom, ! [V_PH, V_PS] : (proved(imp(V_PH,imp(V_PS,V_PH))))).
fof(rule_ax_2, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(imp(V_PH,imp(V_PS,V_CH)),imp(imp(V_PH,V_PS),imp(V_PH,V_CH)))))).
fof(rule_ax_3, axiom, ! [V_PH, V_PS] : (proved(imp(imp(neg(V_PH),neg(V_PS)),imp(V_PS,V_PH))))).
fof(hypothesis_1, axiom, proved(imp(neg(f_ph_183),f_ch_183))).
fof(hypothesis_2, axiom, proved(imp(f_ps_183,f_ch_183))).
fof(target, conjecture, proved(imp(imp(f_ph_183,f_ps_183),f_ch_183))).
