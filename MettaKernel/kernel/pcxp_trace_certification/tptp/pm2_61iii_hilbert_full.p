% set.mm revision: 47e6e06b87581cd630d210dc41cf83b02eea78ea
% set.mm SHA-256: 3aecffcfcab6f6e114cce1d873a8300d7f41f24928648c04164aaa305b1f491a
% target: pm2.61iii (index 182)
% theory policy: full
% No target proof labels are inputs.
fof(rule_ax_mp, axiom, ! [V_PH, V_PS] : (((proved(V_PH) & proved(imp(V_PH,V_PS))) => proved(V_PS)))).
fof(rule_ax_1, axiom, ! [V_PH, V_PS] : (proved(imp(V_PH,imp(V_PS,V_PH))))).
fof(rule_ax_2, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(imp(V_PH,imp(V_PS,V_CH)),imp(imp(V_PH,V_PS),imp(V_PH,V_CH)))))).
fof(rule_ax_3, axiom, ! [V_PH, V_PS] : (proved(imp(imp(neg(V_PH),neg(V_PS)),imp(V_PS,V_PH))))).
fof(rule_mp2, axiom, ! [V_PH, V_PS, V_CH] : (((proved(V_PH) & proved(V_PS) & proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(V_CH)))).
fof(rule_mp2b, axiom, ! [V_PH, V_PS, V_CH] : (((proved(V_PH) & proved(imp(V_PH,V_PS)) & proved(imp(V_PS,V_CH))) => proved(V_CH)))).
fof(rule_a1i, axiom, ! [V_PH, V_PS] : (((proved(V_PH)) => proved(imp(V_PS,V_PH))))).
fof(rule_2a1i, axiom, ! [V_PH, V_PS, V_CH] : (((proved(V_PH)) => proved(imp(V_PS,imp(V_CH,V_PH)))))).
fof(rule_mp1i, axiom, ! [V_PH, V_PS, V_CH] : (((proved(V_PH) & proved(imp(V_PH,V_PS))) => proved(imp(V_CH,V_PS))))).
fof(rule_a2i, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(imp(imp(V_PH,V_PS),imp(V_PH,V_CH)))))).
fof(rule_mpd, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(imp(V_PH,V_CH))))).
fof(rule_imim2i, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,V_PS))) => proved(imp(imp(V_CH,V_PH),imp(V_CH,V_PS)))))).
fof(rule_syl, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_PS,V_CH))) => proved(imp(V_PH,V_CH))))).
fof(rule_3syl, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_PS,V_CH)) & proved(imp(V_CH,V_TH))) => proved(imp(V_PH,V_TH))))).
fof(rule_4syl, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_PS,V_CH)) & proved(imp(V_CH,V_TH)) & proved(imp(V_TH,V_TA))) => proved(imp(V_PH,V_TA))))).
fof(rule_mpi, axiom, ! [V_PS, V_PH, V_CH] : (((proved(V_PS) & proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(imp(V_PH,V_CH))))).
fof(rule_mpisyl, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,V_PS)) & proved(V_CH) & proved(imp(V_PS,imp(V_CH,V_TH)))) => proved(imp(V_PH,V_TH))))).
fof(rule_id, axiom, ! [V_PH] : (proved(imp(V_PH,V_PH)))).
fof(rule_idalt, axiom, ! [V_PH] : (proved(imp(V_PH,V_PH)))).
fof(rule_idd, axiom, ! [V_PH, V_PS] : (proved(imp(V_PH,imp(V_PS,V_PS))))).
fof(rule_a1d, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,V_PS))) => proved(imp(V_PH,imp(V_CH,V_PS)))))).
fof(rule_2a1d, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,V_PS))) => proved(imp(V_PH,imp(V_CH,imp(V_TH,V_PS))))))).
fof(rule_a1i13, axiom, ! [V_PS, V_TH, V_PH, V_CH] : (((proved(imp(V_PS,V_TH))) => proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH))))))).
fof(rule_2a1, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(V_PH,imp(V_PS,imp(V_CH,V_PH)))))).
fof(rule_a2d, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH))))) => proved(imp(V_PH,imp(imp(V_PS,V_CH),imp(V_PS,V_TH))))))).
fof(rule_sylcom, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_PS,imp(V_CH,V_TH)))) => proved(imp(V_PH,imp(V_PS,V_TH)))))).
fof(rule_syl5com, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_CH,imp(V_PS,V_TH)))) => proved(imp(V_PH,imp(V_CH,V_TH)))))).
fof(rule_com12, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(imp(V_PS,imp(V_PH,V_CH)))))).
fof(rule_syl11, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_TH,V_PH))) => proved(imp(V_PS,imp(V_TH,V_CH)))))).
fof(rule_syl5, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_CH,imp(V_PS,V_TH)))) => proved(imp(V_CH,imp(V_PH,V_TH)))))).
fof(rule_syl6, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_CH,V_TH))) => proved(imp(V_PH,imp(V_PS,V_TH)))))).
fof(rule_syl56, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_CH,imp(V_PS,V_TH))) & proved(imp(V_TH,V_TA))) => proved(imp(V_CH,imp(V_PH,V_TA)))))).
fof(rule_syl6com, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_CH,V_TH))) => proved(imp(V_PS,imp(V_PH,V_TH)))))).
fof(rule_mpcom, axiom, ! [V_PS, V_PH, V_CH] : (((proved(imp(V_PS,V_PH)) & proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(imp(V_PS,V_CH))))).
fof(rule_syli, axiom, ! [V_PS, V_PH, V_CH, V_TH] : (((proved(imp(V_PS,imp(V_PH,V_CH))) & proved(imp(V_CH,imp(V_PH,V_TH)))) => proved(imp(V_PS,imp(V_PH,V_TH)))))).
fof(rule_syl2im, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_CH,V_TH)) & proved(imp(V_PS,imp(V_TH,V_TA)))) => proved(imp(V_PH,imp(V_CH,V_TA)))))).
fof(rule_syl2imc, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_CH,V_TH)) & proved(imp(V_PS,imp(V_TH,V_TA)))) => proved(imp(V_CH,imp(V_PH,V_TA)))))).
fof(rule_pm2_27, axiom, ! [V_PH, V_PS] : (proved(imp(V_PH,imp(imp(V_PH,V_PS),V_PS))))).
fof(rule_mpdd, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH))))) => proved(imp(V_PH,imp(V_PS,V_TH)))))).
fof(rule_mpid, axiom, ! [V_PH, V_CH, V_PS, V_TH] : (((proved(imp(V_PH,V_CH)) & proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH))))) => proved(imp(V_PH,imp(V_PS,V_TH)))))).
fof(rule_mpdi, axiom, ! [V_PS, V_CH, V_PH, V_TH] : (((proved(imp(V_PS,V_CH)) & proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH))))) => proved(imp(V_PH,imp(V_PS,V_TH)))))).
fof(rule_mpii, axiom, ! [V_CH, V_PH, V_PS, V_TH] : (((proved(V_CH) & proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH))))) => proved(imp(V_PH,imp(V_PS,V_TH)))))).
fof(rule_syld, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_PH,imp(V_CH,V_TH)))) => proved(imp(V_PH,imp(V_PS,V_TH)))))).
fof(rule_syldc, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_PH,imp(V_CH,V_TH)))) => proved(imp(V_PS,imp(V_PH,V_TH)))))).
fof(rule_mp2d, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_PH,V_CH)) & proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH))))) => proved(imp(V_PH,V_TH))))).
fof(rule_a1dd, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(imp(V_PH,imp(V_PS,imp(V_TH,V_CH))))))).
fof(rule_2a1dd, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(imp(V_PH,imp(V_PS,imp(V_TH,imp(V_TA,V_CH)))))))).
fof(rule_pm2_43i, axiom, ! [V_PH, V_PS] : (((proved(imp(V_PH,imp(V_PH,V_PS)))) => proved(imp(V_PH,V_PS))))).
fof(rule_pm2_43d, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(V_PS,imp(V_PS,V_CH))))) => proved(imp(V_PH,imp(V_PS,V_CH)))))).
fof(rule_pm2_43a, axiom, ! [V_PS, V_PH, V_CH] : (((proved(imp(V_PS,imp(V_PH,imp(V_PS,V_CH))))) => proved(imp(V_PS,imp(V_PH,V_CH)))))).
fof(rule_pm2_43b, axiom, ! [V_PS, V_PH, V_CH] : (((proved(imp(V_PS,imp(V_PH,imp(V_PS,V_CH))))) => proved(imp(V_PH,imp(V_PS,V_CH)))))).
fof(rule_pm2_43, axiom, ! [V_PH, V_PS] : (proved(imp(imp(V_PH,imp(V_PH,V_PS)),imp(V_PH,V_PS))))).
fof(rule_imim2d, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(imp(V_PH,imp(imp(V_TH,V_PS),imp(V_TH,V_CH))))))).
fof(rule_imim2, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(imp(V_PH,V_PS),imp(imp(V_CH,V_PH),imp(V_CH,V_PS)))))).
fof(rule_embantd, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_PH,imp(V_CH,V_TH)))) => proved(imp(V_PH,imp(imp(V_PS,V_CH),V_TH)))))).
fof(rule_3syld, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_PH,imp(V_CH,V_TH))) & proved(imp(V_PH,imp(V_TH,V_TA)))) => proved(imp(V_PH,imp(V_PS,V_TA)))))).
fof(rule_sylsyld, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_PH,imp(V_CH,V_TH))) & proved(imp(V_PS,imp(V_TH,V_TA)))) => proved(imp(V_PH,imp(V_CH,V_TA)))))).
fof(rule_imim12i, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_CH,V_TH))) => proved(imp(imp(V_PS,V_CH),imp(V_PH,V_TH)))))).
fof(rule_imim1i, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,V_PS))) => proved(imp(imp(V_PS,V_CH),imp(V_PH,V_CH)))))).
fof(rule_imim3i, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(imp(imp(V_TH,V_PH),imp(imp(V_TH,V_PS),imp(V_TH,V_CH))))))).
fof(rule_sylc, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_PH,V_CH)) & proved(imp(V_PS,imp(V_CH,V_TH)))) => proved(imp(V_PH,V_TH))))).
fof(rule_syl3c, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_PH,V_CH)) & proved(imp(V_PH,V_TH)) & proved(imp(V_PS,imp(V_CH,imp(V_TH,V_TA))))) => proved(imp(V_PH,V_TA))))).
fof(rule_syl6mpi, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(V_TH) & proved(imp(V_CH,imp(V_TH,V_TA)))) => proved(imp(V_PH,imp(V_PS,V_TA)))))).
fof(rule_mpsyl, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(V_PH) & proved(imp(V_PS,V_CH)) & proved(imp(V_PH,imp(V_CH,V_TH)))) => proved(imp(V_PS,V_TH))))).
fof(rule_mpsylsyld, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(V_PH) & proved(imp(V_PS,imp(V_CH,V_TH))) & proved(imp(V_PH,imp(V_TH,V_TA)))) => proved(imp(V_PS,imp(V_CH,V_TA)))))).
fof(rule_syl6c, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_PH,imp(V_PS,V_TH))) & proved(imp(V_CH,imp(V_TH,V_TA)))) => proved(imp(V_PH,imp(V_PS,V_TA)))))).
fof(rule_syl6ci, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_PH,V_TH)) & proved(imp(V_CH,imp(V_TH,V_TA)))) => proved(imp(V_PH,imp(V_PS,V_TA)))))).
fof(rule_syldd, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH)))) & proved(imp(V_PH,imp(V_PS,imp(V_TH,V_TA))))) => proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TA))))))).
fof(rule_syl5d, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_PH,imp(V_TH,imp(V_CH,V_TA))))) => proved(imp(V_PH,imp(V_TH,imp(V_PS,V_TA))))))).
fof(rule_syl7, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_CH,imp(V_TH,imp(V_PS,V_TA))))) => proved(imp(V_CH,imp(V_TH,imp(V_PH,V_TA))))))).
fof(rule_syl6d, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH)))) & proved(imp(V_PH,imp(V_TH,V_TA)))) => proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TA))))))).
fof(rule_syl8, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH)))) & proved(imp(V_TH,V_TA))) => proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TA))))))).
fof(rule_syl9, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_TH,imp(V_CH,V_TA)))) => proved(imp(V_PH,imp(V_TH,imp(V_PS,V_TA))))))).
fof(rule_syl9r, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_TH,imp(V_CH,V_TA)))) => proved(imp(V_TH,imp(V_PH,imp(V_PS,V_TA))))))).
fof(rule_syl10, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA, V_ET] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_PH,imp(V_PS,imp(V_TH,V_TA)))) & proved(imp(V_CH,imp(V_TA,V_ET)))) => proved(imp(V_PH,imp(V_PS,imp(V_TH,V_ET))))))).
fof(rule_a1ddd, axiom, ! [V_PH, V_PS, V_CH, V_TA, V_TH] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TA))))) => proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,V_TA)))))))).
fof(rule_imim12d, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_PH,imp(V_TH,V_TA)))) => proved(imp(V_PH,imp(imp(V_CH,V_TH),imp(V_PS,V_TA))))))).
fof(rule_imim1d, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(imp(V_PH,imp(imp(V_CH,V_TH),imp(V_PS,V_TH))))))).
fof(rule_imim1, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(imp(V_PH,V_PS),imp(imp(V_PS,V_CH),imp(V_PH,V_CH)))))).
fof(rule_pm2_83, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (proved(imp(imp(V_PH,imp(V_PS,V_CH)),imp(imp(V_PH,imp(V_CH,V_TH)),imp(V_PH,imp(V_PS,V_TH))))))).
fof(rule_peirceroll, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(imp(imp(imp(V_PH,V_PS),V_PH),V_PH),imp(imp(imp(V_PH,V_PS),V_CH),imp(imp(V_CH,V_PH),V_PH)))))).
fof(rule_com23, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH))))) => proved(imp(V_PH,imp(V_CH,imp(V_PS,V_TH))))))).
fof(rule_com3r, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH))))) => proved(imp(V_CH,imp(V_PH,imp(V_PS,V_TH))))))).
fof(rule_com13, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH))))) => proved(imp(V_CH,imp(V_PS,imp(V_PH,V_TH))))))).
fof(rule_com3l, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH))))) => proved(imp(V_PS,imp(V_CH,imp(V_PH,V_TH))))))).
fof(rule_pm2_04, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(imp(V_PH,imp(V_PS,V_CH)),imp(V_PS,imp(V_PH,V_CH)))))).
fof(rule_com34, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,V_TA)))))) => proved(imp(V_PH,imp(V_PS,imp(V_TH,imp(V_CH,V_TA)))))))).
fof(rule_com4l, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,V_TA)))))) => proved(imp(V_PS,imp(V_CH,imp(V_TH,imp(V_PH,V_TA)))))))).
fof(rule_com4t, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,V_TA)))))) => proved(imp(V_CH,imp(V_TH,imp(V_PH,imp(V_PS,V_TA)))))))).
fof(rule_com4r, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,V_TA)))))) => proved(imp(V_TH,imp(V_PH,imp(V_PS,imp(V_CH,V_TA)))))))).
fof(rule_com24, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,V_TA)))))) => proved(imp(V_PH,imp(V_TH,imp(V_CH,imp(V_PS,V_TA)))))))).
fof(rule_com14, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,V_TA)))))) => proved(imp(V_TH,imp(V_PS,imp(V_CH,imp(V_PH,V_TA)))))))).
fof(rule_com45, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA, V_ET] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,imp(V_TA,V_ET))))))) => proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TA,imp(V_TH,V_ET))))))))).
fof(rule_com35, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA, V_ET] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,imp(V_TA,V_ET))))))) => proved(imp(V_PH,imp(V_PS,imp(V_TA,imp(V_TH,imp(V_CH,V_ET))))))))).
fof(rule_com25, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA, V_ET] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,imp(V_TA,V_ET))))))) => proved(imp(V_PH,imp(V_TA,imp(V_CH,imp(V_TH,imp(V_PS,V_ET))))))))).
fof(rule_com5l, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA, V_ET] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,imp(V_TA,V_ET))))))) => proved(imp(V_PS,imp(V_CH,imp(V_TH,imp(V_TA,imp(V_PH,V_ET))))))))).
fof(rule_com15, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA, V_ET] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,imp(V_TA,V_ET))))))) => proved(imp(V_TA,imp(V_PS,imp(V_CH,imp(V_TH,imp(V_PH,V_ET))))))))).
fof(rule_com52l, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA, V_ET] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,imp(V_TA,V_ET))))))) => proved(imp(V_CH,imp(V_TH,imp(V_TA,imp(V_PH,imp(V_PS,V_ET))))))))).
fof(rule_com52r, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA, V_ET] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,imp(V_TA,V_ET))))))) => proved(imp(V_TH,imp(V_TA,imp(V_PH,imp(V_PS,imp(V_CH,V_ET))))))))).
fof(rule_com5r, axiom, ! [V_PH, V_PS, V_CH, V_TH, V_TA, V_ET] : (((proved(imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,imp(V_TA,V_ET))))))) => proved(imp(V_TA,imp(V_PH,imp(V_PS,imp(V_CH,imp(V_TH,V_ET))))))))).
fof(rule_imim12, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (proved(imp(imp(V_PH,V_PS),imp(imp(V_CH,V_TH),imp(imp(V_PS,V_CH),imp(V_PH,V_TH))))))).
fof(rule_jarr, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(imp(imp(V_PH,V_PS),V_CH),imp(V_PS,V_CH))))).
fof(rule_jarri, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(imp(V_PH,V_PS),V_CH))) => proved(imp(V_PS,V_CH))))).
fof(rule_pm2_86d, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(imp(V_PS,V_CH),imp(V_PS,V_TH))))) => proved(imp(V_PH,imp(V_PS,imp(V_CH,V_TH))))))).
fof(rule_pm2_86, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(imp(imp(V_PH,V_PS),imp(V_PH,V_CH)),imp(V_PH,imp(V_PS,V_CH)))))).
fof(rule_pm2_86i, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(imp(V_PH,V_PS),imp(V_PH,V_CH)))) => proved(imp(V_PH,imp(V_PS,V_CH)))))).
fof(rule_loolin, axiom, ! [V_PH, V_PS] : (proved(imp(imp(imp(V_PH,V_PS),imp(V_PS,V_PH)),imp(V_PS,V_PH))))).
fof(rule_loowoz, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(imp(imp(V_PH,V_PS),imp(V_PH,V_CH)),imp(imp(V_PS,V_PH),imp(V_PS,V_CH)))))).
fof(rule_con4, axiom, ! [V_PH, V_PS] : (proved(imp(imp(neg(V_PH),neg(V_PS)),imp(V_PS,V_PH))))).
fof(rule_con4i, axiom, ! [V_PH, V_PS] : (((proved(imp(neg(V_PH),neg(V_PS)))) => proved(imp(V_PS,V_PH))))).
fof(rule_con4d, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(neg(V_PS),neg(V_CH))))) => proved(imp(V_PH,imp(V_CH,V_PS)))))).
fof(rule_mt4, axiom, ! [V_PH, V_PS] : (((proved(V_PH) & proved(imp(neg(V_PS),neg(V_PH)))) => proved(V_PS)))).
fof(rule_mt4d, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_PH,imp(neg(V_CH),neg(V_PS))))) => proved(imp(V_PH,V_CH))))).
fof(rule_mt4i, axiom, ! [V_CH, V_PH, V_PS] : (((proved(V_CH) & proved(imp(V_PH,imp(neg(V_PS),neg(V_CH))))) => proved(imp(V_PH,V_PS))))).
fof(rule_pm2_21i, axiom, ! [V_PH, V_PS] : (((proved(neg(V_PH))) => proved(imp(V_PH,V_PS))))).
fof(rule_pm2_24ii, axiom, ! [V_PH, V_PS] : (((proved(V_PH) & proved(neg(V_PH))) => proved(V_PS)))).
fof(rule_pm2_21d, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,neg(V_PS)))) => proved(imp(V_PH,imp(V_PS,V_CH)))))).
fof(rule_pm2_21ddalt, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_PH,neg(V_PS)))) => proved(imp(V_PH,V_CH))))).
fof(rule_pm2_21, axiom, ! [V_PH, V_PS] : (proved(imp(neg(V_PH),imp(V_PH,V_PS))))).
fof(rule_pm2_24, axiom, ! [V_PH, V_PS] : (proved(imp(V_PH,imp(neg(V_PH),V_PS))))).
fof(rule_jarl, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(imp(imp(V_PH,V_PS),V_CH),imp(neg(V_PH),V_CH))))).
fof(rule_jarli, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(imp(V_PH,V_PS),V_CH))) => proved(imp(neg(V_PH),V_CH))))).
fof(rule_pm2_18d, axiom, ! [V_PH, V_PS] : (((proved(imp(V_PH,imp(neg(V_PS),V_PS)))) => proved(imp(V_PH,V_PS))))).
fof(rule_pm2_18, axiom, ! [V_PH] : (proved(imp(imp(neg(V_PH),V_PH),V_PH)))).
fof(rule_pm2_18i, axiom, ! [V_PH] : (((proved(imp(neg(V_PH),V_PH))) => proved(V_PH)))).
fof(rule_notnotr, axiom, ! [V_PH] : (proved(imp(neg(neg(V_PH)),V_PH)))).
fof(rule_notnotri, axiom, ! [V_PH] : (((proved(neg(neg(V_PH)))) => proved(V_PH)))).
fof(rule_notnotrialt, axiom, ! [V_PH] : (((proved(neg(neg(V_PH)))) => proved(V_PH)))).
fof(rule_notnotrd, axiom, ! [V_PH, V_PS] : (((proved(imp(V_PH,neg(neg(V_PS))))) => proved(imp(V_PH,V_PS))))).
fof(rule_con2d, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(V_PS,neg(V_CH))))) => proved(imp(V_PH,imp(V_CH,neg(V_PS))))))).
fof(rule_con2, axiom, ! [V_PH, V_PS] : (proved(imp(imp(V_PH,neg(V_PS)),imp(V_PS,neg(V_PH)))))).
fof(rule_mt2d, axiom, ! [V_PH, V_CH, V_PS] : (((proved(imp(V_PH,V_CH)) & proved(imp(V_PH,imp(V_PS,neg(V_CH))))) => proved(imp(V_PH,neg(V_PS)))))).
fof(rule_mt2i, axiom, ! [V_CH, V_PH, V_PS] : (((proved(V_CH) & proved(imp(V_PH,imp(V_PS,neg(V_CH))))) => proved(imp(V_PH,neg(V_PS)))))).
fof(rule_nsyl3, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,neg(V_PS))) & proved(imp(V_CH,V_PS))) => proved(imp(V_CH,neg(V_PH)))))).
fof(rule_con2i, axiom, ! [V_PH, V_PS] : (((proved(imp(V_PH,neg(V_PS)))) => proved(imp(V_PS,neg(V_PH)))))).
fof(rule_nsyl, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,neg(V_PS))) & proved(imp(V_CH,V_PS))) => proved(imp(V_PH,neg(V_CH)))))).
fof(rule_nsyl2, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,neg(V_PS))) & proved(imp(neg(V_CH),V_PS))) => proved(imp(V_PH,V_CH))))).
fof(rule_notnot, axiom, ! [V_PH] : (proved(imp(V_PH,neg(neg(V_PH)))))).
fof(rule_notnoti, axiom, ! [V_PH] : (((proved(V_PH)) => proved(neg(neg(V_PH)))))).
fof(rule_notnotd, axiom, ! [V_PH, V_PS] : (((proved(imp(V_PH,V_PS))) => proved(imp(V_PH,neg(neg(V_PS))))))).
fof(rule_con1d, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(neg(V_PS),V_CH)))) => proved(imp(V_PH,imp(neg(V_CH),V_PS)))))).
fof(rule_con1, axiom, ! [V_PH, V_PS] : (proved(imp(imp(neg(V_PH),V_PS),imp(neg(V_PS),V_PH))))).
fof(rule_con1i, axiom, ! [V_PH, V_PS] : (((proved(imp(neg(V_PH),V_PS))) => proved(imp(neg(V_PS),V_PH))))).
fof(rule_mt3d, axiom, ! [V_PH, V_CH, V_PS] : (((proved(imp(V_PH,neg(V_CH))) & proved(imp(V_PH,imp(neg(V_PS),V_CH)))) => proved(imp(V_PH,V_PS))))).
fof(rule_mt3i, axiom, ! [V_CH, V_PH, V_PS] : (((proved(neg(V_CH)) & proved(imp(V_PH,imp(neg(V_PS),V_CH)))) => proved(imp(V_PH,V_PS))))).
fof(rule_pm2_24i, axiom, ! [V_PH, V_PS] : (((proved(V_PH)) => proved(imp(neg(V_PH),V_PS))))).
fof(rule_pm2_24d, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,V_PS))) => proved(imp(V_PH,imp(neg(V_PS),V_CH)))))).
fof(rule_con3d, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(imp(V_PH,imp(neg(V_CH),neg(V_PS))))))).
fof(rule_con3, axiom, ! [V_PH, V_PS] : (proved(imp(imp(V_PH,V_PS),imp(neg(V_PS),neg(V_PH)))))).
fof(rule_con3i, axiom, ! [V_PH, V_PS] : (((proved(imp(V_PH,V_PS))) => proved(imp(neg(V_PS),neg(V_PH)))))).
fof(rule_con3rr3, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(imp(neg(V_CH),imp(V_PH,neg(V_PS))))))).
fof(rule_nsyld, axiom, ! [V_PH, V_PS, V_CH, V_TA] : (((proved(imp(V_PH,imp(V_PS,neg(V_CH)))) & proved(imp(V_PH,imp(V_TA,V_CH)))) => proved(imp(V_PH,imp(V_PS,neg(V_TA))))))).
fof(rule_nsyli, axiom, ! [V_PH, V_PS, V_CH, V_TH] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_TH,neg(V_CH)))) => proved(imp(V_PH,imp(V_TH,neg(V_PS))))))).
fof(rule_nsyl4, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,V_PS)) & proved(imp(neg(V_PH),V_CH))) => proved(imp(neg(V_CH),V_PS))))).
fof(rule_nsyl5, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,V_PS)) & proved(imp(neg(V_PH),V_CH))) => proved(imp(neg(V_PS),V_CH))))).
fof(rule_pm3_2im, axiom, ! [V_PH, V_PS] : (proved(imp(V_PH,imp(V_PS,neg(imp(V_PH,neg(V_PS)))))))).
fof(rule_jc, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_PH,V_CH))) => proved(imp(V_PH,neg(imp(V_PS,neg(V_CH)))))))).
fof(rule_jcn, axiom, ! [V_PH, V_PS] : (proved(imp(V_PH,imp(neg(V_PS),neg(imp(V_PH,V_PS))))))).
fof(rule_jcnd, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,V_PS)) & proved(imp(V_PH,neg(V_CH)))) => proved(imp(V_PH,neg(imp(V_PS,V_CH))))))).
fof(rule_impi, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(V_PS,V_CH)))) => proved(imp(neg(imp(V_PH,neg(V_PS))),V_CH))))).
fof(rule_expi, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(neg(imp(V_PH,neg(V_PS))),V_CH))) => proved(imp(V_PH,imp(V_PS,V_CH)))))).
fof(rule_simprim, axiom, ! [V_PH, V_PS] : (proved(imp(neg(imp(V_PH,neg(V_PS))),V_PS)))).
fof(rule_simplim, axiom, ! [V_PH, V_PS] : (proved(imp(neg(imp(V_PH,V_PS)),V_PH)))).
fof(rule_pm2_5g, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(neg(imp(V_PH,V_PS)),imp(neg(V_PH),V_CH))))).
fof(rule_pm2_5, axiom, ! [V_PH, V_PS] : (proved(imp(neg(imp(V_PH,V_PS)),imp(neg(V_PH),V_PS))))).
fof(rule_conax1, axiom, ! [V_PH, V_PS] : (proved(imp(neg(imp(V_PH,V_PS)),neg(V_PS))))).
fof(rule_conax1k, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(neg(imp(V_PH,V_PS)),imp(V_CH,neg(V_PS)))))).
fof(rule_pm2_51, axiom, ! [V_PH, V_PS] : (proved(imp(neg(imp(V_PH,V_PS)),imp(V_PH,neg(V_PS)))))).
fof(rule_pm2_52, axiom, ! [V_PH, V_PS] : (proved(imp(neg(imp(V_PH,V_PS)),imp(neg(V_PH),neg(V_PS)))))).
fof(rule_pm2_521g, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(neg(imp(V_PH,V_PS)),imp(V_PS,V_CH))))).
fof(rule_pm2_521g2, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(neg(imp(V_PH,V_PS)),imp(V_CH,V_PH))))).
fof(rule_pm2_521, axiom, ! [V_PH, V_PS] : (proved(imp(neg(imp(V_PH,V_PS)),imp(V_PS,V_PH))))).
fof(rule_expt, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(imp(neg(imp(V_PH,neg(V_PS))),V_CH),imp(V_PH,imp(V_PS,V_CH)))))).
fof(rule_impt, axiom, ! [V_PH, V_PS, V_CH] : (proved(imp(imp(V_PH,imp(V_PS,V_CH)),imp(neg(imp(V_PH,neg(V_PS))),V_CH))))).
fof(rule_pm2_61d, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(V_PH,imp(neg(V_PS),V_CH)))) => proved(imp(V_PH,V_CH))))).
fof(rule_pm2_61d1, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(neg(V_PS),V_CH))) => proved(imp(V_PH,V_CH))))).
fof(rule_pm2_61d2, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(neg(V_PS),V_CH))) & proved(imp(V_PS,V_CH))) => proved(imp(V_PH,V_CH))))).
fof(rule_pm2_61i, axiom, ! [V_PH, V_PS] : (((proved(imp(V_PH,V_PS)) & proved(imp(neg(V_PH),V_PS))) => proved(V_PS)))).
fof(rule_pm2_61ii, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(neg(V_PH),imp(neg(V_PS),V_CH))) & proved(imp(V_PH,V_CH)) & proved(imp(V_PS,V_CH))) => proved(V_CH)))).
fof(rule_pm2_61nii, axiom, ! [V_PH, V_PS, V_CH] : (((proved(imp(V_PH,imp(V_PS,V_CH))) & proved(imp(neg(V_PH),V_CH)) & proved(imp(neg(V_PS),V_CH))) => proved(V_CH)))).
fof(hypothesis_1, axiom, proved(imp(neg(f_ph_182),imp(neg(f_ps_182),imp(neg(f_ch_182),f_th_182))))).
fof(hypothesis_2, axiom, proved(imp(f_ph_182,f_th_182))).
fof(hypothesis_3, axiom, proved(imp(f_ps_182,f_th_182))).
fof(hypothesis_4, axiom, proved(imp(f_ch_182,f_th_182))).
fof(target, conjecture, proved(f_th_182)).
