% set.mm revision: 47e6e06b87581cd630d210dc41cf83b02eea78ea
% set.mm SHA-256: 3aecffcfcab6f6e114cce1d873a8300d7f41f24928648c04164aaa305b1f491a
% target: pm2.61nii (index 181)
% theory policy: reference
% Calibration only: theory labels come from the stored proof.
fof(rule_pm2_61d1, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(neg(V_PS),V_CH))) => proved(imp(V_PH,V_CH))))).
fof(rule_pm2_61i, axiom, ! [V_PH, V_PS] : (((proved(imp(V_PH,V_PS)) & proved(imp(neg(V_PH),V_PS))) => proved(V_PS)))).
fof(hypothesis_1, axiom, proved(imp(f_ph_181,imp(f_ps_181,f_ch_181)))).
fof(hypothesis_2, axiom, proved(imp(neg(f_ph_181),f_ch_181))).
fof(hypothesis_3, axiom, proved(imp(neg(f_ps_181),f_ch_181))).
fof(target, conjecture, proved(f_ch_181)).
