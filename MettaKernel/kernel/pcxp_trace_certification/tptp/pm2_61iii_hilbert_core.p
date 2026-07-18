% set.mm revision: 47e6e06b87581cd630d210dc41cf83b02eea78ea
% set.mm SHA-256: 3aecffcfcab6f6e114cce1d873a8300d7f41f24928648c04164aaa305b1f491a
% target: pm2.61iii (index 182)
% theory policy: core
% No target proof labels are inputs.
fof(rule_ax_mp, axiom, ! [V_PH, V_PS] : (((proved(V_PH) & proved(imp(V_PH,V_PS))) => proved(V_PS)))).
fof(rule_ax_1, axiom, ! [V_PH, V_PS] : (proved(imp(V_PH,imp(V_PS,V_PH))))).
fof(rule_ax_2, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(imp(V_PH,imp(V_PS,V_CH)),imp(imp(V_PH,V_PS),imp(V_PH,V_CH)))))).
fof(rule_ax_3, axiom, ! [V_PH, V_PS] : (proved(imp(imp(neg(V_PH),neg(V_PS)),imp(V_PS,V_PH))))).
fof(hypothesis_1, axiom, proved(imp(neg(f_ph_182),imp(neg(f_ps_182),imp(neg(f_ch_182),f_th_182))))).
fof(hypothesis_2, axiom, proved(imp(f_ph_182,f_th_182))).
fof(hypothesis_3, axiom, proved(imp(f_ps_182,f_th_182))).
fof(hypothesis_4, axiom, proved(imp(f_ch_182,f_th_182))).
fof(target, conjecture, proved(f_th_182)).
