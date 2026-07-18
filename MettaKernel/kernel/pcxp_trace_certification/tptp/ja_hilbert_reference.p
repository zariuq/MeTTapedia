% set.mm revision: 47e6e06b87581cd630d210dc41cf83b02eea78ea
% set.mm SHA-256: 3aecffcfcab6f6e114cce1d873a8300d7f41f24928648c04164aaa305b1f491a
% target: ja (index 183)
% theory policy: reference
% Calibration only: theory labels come from the stored proof.
fof(rule_imim2i, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,V_PS))) => proved(imp(imp(V_CH,V_PH),imp(V_CH,V_PS)))))).
fof(rule_pm2_61d1, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(neg(V_PS),V_CH))) => proved(imp(V_PH,V_CH))))).
fof(hypothesis_1, axiom, proved(imp(neg(f_ph_183),f_ch_183))).
fof(hypothesis_2, axiom, proved(imp(f_ps_183,f_ch_183))).
fof(target, conjecture, proved(imp(imp(f_ph_183,f_ps_183),f_ch_183))).
