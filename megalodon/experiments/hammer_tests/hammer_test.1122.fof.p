fof(c_Subq,axiom,(! [X0:$i] : (! [X1:$i] : (c_Subq(c_X0,c_X1) <=> (! [X2] : (c_In(X2,c_X0) => c_In(X2,c_X1))))))). % 8a8e36b858cd07fc5e5f164d8075dc68a88221ed1e4c9f28dac4a6fdb2172e87
fof(set_5Fext,axiom,(! [X0] : (! [X1] : (c_Subq(X0,X1) => (c_Subq(X1,X0) => (X0 = X1)))))). % 5189b0389a1efe35ba744aa1436bb23541e75e8a85658313375e1e0b3321128f
fof(c_EmptyAx,axiom,~ (? [X0] : c_In(X0,c_Empty))). % 920f955f033a1286fcaba96c8eb55d2079812a3041ff6b812df4cc2636156b59
fof(c_UnionEq,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Union(X0)) <=> (? [X2] : (c_In(X1,X2) & c_In(X2,X0))))))). % 0b67fbe4188c03468f8cd69c462ea8e5fb2269bf1fd67125a6456853d4ab7c74
fof(c_PowerEq,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Power(X0)) <=> c_Subq(X1,X0))))). % b492ab96942311595fd53c93243cb7ab5314986bb8460d580d9382dfab90f7d1
fof(c_TransSet,axiom,(! [X0:$i] : (c_TransSet(c_X0) <=> (! [X1] : (c_In(X1,c_X0) => c_Subq(X1,c_X0)))))). % e7493d5f5a73b6cb40310f6fcb87d02b2965921a25ab96d312adf7eb8157e4b3
fof(c_Union_5Fclosed,axiom,(! [X0:$i] : (c_Union_5Fclosed(c_X0) <=> (! [X1] : (c_In(X1,c_X0) => c_In(c_Union(X1),c_X0)))))). % 54850182033d0575e98bc2b12aa8b9baaa7a541e9d5abc7fddeb74fc5d0a19ac
fof(c_Power_5Fclosed,axiom,(! [X0:$i] : (c_Power_5Fclosed(c_X0) <=> (! [X1] : (c_In(X1,c_X0) => c_In(c_Power(X1),c_X0)))))). % 5a811b601343da9ff9d05d188d672be567de94b980bbbe0e04e628d817f4c7ac
fof(c_ZF_5Fclosed,axiom,(! [X0:$i] : (c_ZF_5Fclosed(c_X0) <=> ((c_Union_5Fclosed(c_X0) & c_Power_5Fclosed(c_X0)) & c_Repl_5Fclosed(c_X0))))). % 43f34d6a2314b56cb12bf5cf84f271f3f02a3e68417b09404cc73152523dbfa0
fof(c_UnivOf_5FIn,axiom,(! [X0] : c_In(X0,c_UnivOf(X0)))). % 64ad93d240a001e91d619642c36f7ea8387780b9860b748f282d12bc22d4a677
fof(c_UnivOf_5FTransSet,axiom,(! [X0] : c_TransSet(c_UnivOf(X0)))). % 40723e6db0df4f3bce8b35ba709f46fd1f4a94f61bdd2e206b8d4e21ea660332
fof(c_UnivOf_5FZF_5Fclosed,axiom,(! [X0] : c_ZF_5Fclosed(c_UnivOf(X0)))). % 4181a4a1a92ac574d2c6208a18ed79b8773a8c1de9330f96e76e3edabcf083ea
fof(c_UnivOf_5FMin,axiom,(! [X0] : (! [X1] : (c_In(X0,X1) => (c_TransSet(X1) => (c_ZF_5Fclosed(X1) => c_Subq(c_UnivOf(X0),X1))))))). % 9a6fd4292d63e7be0caf7c85f8d8c56e3be3c23ff46c2001263cd459da21e6ed
fof(nIn,axiom,(! [X0:$i] : (! [X1:$i] : (nIn(c_X0,c_X1) <=> ~ c_In(c_X0,c_X1))))). % 2f8b7f287504f141b0f821928ac62823a377717763a224067702eee02fc1f359
fof(c_EmptyE,axiom,(! [X0] : nIn(X0,c_Empty))). % db69db5fe0ab30c62cbb6c6a5585580d13a89b7a739501bf6ab7f69ba07ed65e
fof(c_PowerI,axiom,(! [X0] : (! [X1] : (c_Subq(X1,X0) => c_In(X1,c_Power(X0)))))). % 8ec4fb130787ca0a60ebd05ea54a7a9f309a462585bcc1ee86952371bbf7d709
fof(c_Subq_5FEmpty,axiom,(! [X0] : c_Subq(c_Empty,X0))). % ec40ffd5e1efa2305904493e93693c9ded9ce1a6c83c767acc34b0a727c8c8ff
fof(c_Empty_5FIn_5FPower,axiom,(! [X0] : c_In(c_Empty,c_Power(X0)))). % 57bdeb692b87bc968dc5c4c76518265b349fad59aa9d410f1763da99db3af2d7
fof(eq_5Fi_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : ((X0 = X1) => ((X1 = X2) => (X0 = X2))))))). % ebaf3a176014e42e2f894150fb11347d641abecb9be82d29a784bb9b0312d2e8
fof(neq_5Fi_5Fsym,axiom,(! [X0] : (! [X1] : (~ (X0 = X1) => ~ (X1 = X0))))). % 5975ea0d667ef81890db1136e825d1bda7a0dec6bacfabb8f8c03bae6c9d6bde
fof(c_Subq_5Fref,axiom,(! [X0] : c_Subq(X0,X0))). % 8cc027a87882f9d68d5bb3a254ca44809bb1f7acc0d6ad2ed1d5aa7f040b3422
fof(c_Subq_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : (c_Subq(X0,X1) => (c_Subq(X1,X2) => c_Subq(X0,X2))))))). % 065e1c25434d58f32a87cf53ecf8bea2d3e1eb2dc3e022e6bd6f5e03e5f845a5
fof(c_Empty_5FSubq_5Feq,axiom,(! [X0] : (c_Subq(X0,c_Empty) => (X0 = c_Empty)))). % 3eadb639389a682a69e54b191ac296a25a1a39baabdefa25ba9bccbeb7038d35
fof(c_Empty_5Feq,axiom,(! [X0] : ((! [X1] : nIn(X1,X0)) => (X0 = c_Empty)))). % 4b1c3808883170ae2c35267bed4184182595364acf85a55cf81ba0b3c95c9de5
fof(c_UnionI,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X1,X2) => (c_In(X2,X0) => c_In(X1,c_Union(X0)))))))). % 681f08928f47fe62e4803e6fa2b70b4ea7a5d093a6d00273519a068fea82736f
fof(c_UnionE,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Union(X0)) => (? [X2] : (c_In(X1,X2) & c_In(X2,X0))))))). % 704291d62c629bb6d6fba75f33b0b13133e87259f1defdfafd1142825f56775c
fof(c_PowerE,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Power(X0)) => c_Subq(X1,X0))))). % e6c5658300fbb425904a43da92acd1b8285eb12502cbe3e889df5f01952d03f8
fof(c_Self_5FIn_5FPower,axiom,(! [X0] : c_In(X0,c_Power(X0)))). % 9e7d17e9e24e10742a1db89c76f516cfd1d826d9141665d2cdfcc8973b143d8d
fof(c_UPairE,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X0,c_UPair(X1,X2)) => ((X0 = X1) | (X0 = X2))))))). % 27295eee731b2e2ca8dcbae7e034df4ffc68d79fa2eb3e5177a683f5e766fc73
fof(c_UPairI1,axiom,(! [X0] : (! [X1] : c_In(X0,c_UPair(X0,X1))))). % d4cb6fc9a2dc09ce7fcb98d747c419612bff8c7c54b31e61eadaac97237200dc
fof(c_UPairI2,axiom,(! [X0] : (! [X1] : c_In(X1,c_UPair(X0,X1))))). % 17192a1a43d5167598e15fcb1851bd723fde74be514850fe1f482a3de4a622a3
fof(c_Sing,axiom,(! [X0:$i] : (c_Sing(c_X0) = c_UPair(c_X0,c_X0)))). % 158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7
fof(c_SingI,axiom,(! [X0] : c_In(X0,c_Sing(X0)))). % 77b0506ab5458ffa86830e02cd5fb26c1a1bd554e0216a7393a1bc0caac25b87
fof(c_SingE,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Sing(X0)) => (X1 = X0))))). % 032df44ded59d711a15139bdf4096b5420fd1483acfe697faa4c76557c931e91
fof(binunion,axiom,(! [X0:$i] : (! [X1:$i] : (binunion(c_X0,c_X1) = c_Union(c_UPair(c_X0,c_X1)))))). % 0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e
fof(binunionI1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X0) => c_In(X2,binunion(X0,X1))))))). % 9e9f1f4dffcf252f2a92d22b0643d42fab016ee86072c0d9d927a0865dcb1c66
fof(binunionI2,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X1) => c_In(X2,binunion(X0,X1))))))). % c5d368c671e9b46c609a1d230dfb54bcf83cb15c2467e38febbebbaae3b135e5
fof(binunionE,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,binunion(X0,X1)) => (c_In(X2,X0) | c_In(X2,X1))))))). % f270d6aed9b2d86fc0b81ffd22ec16d7b33f0b58017f24581b824b49fb600f05
fof(binunion_5Fasso,axiom,(! [X0] : (! [X1] : (! [X2] : (binunion(X0,binunion(X1,X2)) = binunion(binunion(X0,X1),X2)))))). % 67721cc3000e8d5807e36d600cacd6c66b8482e28b0bfbcdf3a5f78c7eb0f18e
fof(binunion_5Fcom_5FSubq,axiom,(! [X0] : (! [X1] : c_Subq(binunion(X0,X1),binunion(X1,X0))))). % a282be30deb1c298c1256b7a3e4687c02915664d968f0a9c14405d1a1f469395
fof(binunion_5Fcom,axiom,(! [X0] : (! [X1] : (binunion(X0,X1) = binunion(X1,X0))))). % 006fa5505501fe20cccbbc89f12002205a374c3e66a087a028160c507518e332
fof(binunion_5Fidl,axiom,(! [X0] : (binunion(c_Empty,X0) = X0))). % 0d9845e947d190c3e834c5c20eafe01a72e43069e4fab7c05fa73da195474514
fof(binunion_5Fidr,axiom,(! [X0] : (binunion(X0,c_Empty) = X0))). % 9e1ff5e3ef71b4e993dc9b4f0b8a6a1bfbc89716b71b564cfe9d7b2d4e782dc9
fof(binunion_5FSubq_5F1,axiom,(! [X0] : (! [X1] : c_Subq(X0,binunion(X0,X1))))). % 91a0993badea53aedb20396d62ea57d213095e6eef8e9372a21e105c45c931b7
fof(binunion_5FSubq_5F2,axiom,(! [X0] : (! [X1] : c_Subq(X1,binunion(X0,X1))))). % 08072961243ad5b744fa95095981b56ea524a7b80b12f8b044fd9adc9bd624ff
fof(binunion_5FSubq_5Fmin,axiom,(! [X0] : (! [X1] : (! [X2] : (c_Subq(X0,X2) => (c_Subq(X1,X2) => c_Subq(binunion(X0,X1),X2))))))). % 3cf55cc72fc63a566988ee47c2c423883980d19b8bca9f80dd660ff2565ae091
fof(c_SetAdjoin,axiom,(! [X0:$i] : (! [X1:$i] : (c_SetAdjoin(c_X0,c_X1) = binunion(c_X0,c_Sing(c_X1)))))). % 153bff87325a9c7569e721334015eeaf79acf75a785b960eb1b46ee9a5f023f8
fof(binintersectI,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X0) => (c_In(X2,X1) => c_In(X2,binintersect(X0,X1)))))))). % 60326596dd1073df96277e47a8ce32cc389745008f601b6a7af467ea84120040
fof(binintersectE,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,binintersect(X0,X1)) => (c_In(X2,X0) & c_In(X2,X1))))))). % 776f7336d9260a7b2828f159460596cc0a08aad88f391f6eb9376b54a43169d0
fof(binintersectE1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,binintersect(X0,X1)) => c_In(X2,X0)))))). % 96356c122c520f01fe41aa000a6de495dc464356a7c61fe73edc453b21e3f3d0
fof(binintersectE2,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,binintersect(X0,X1)) => c_In(X2,X1)))))). % 6f07a0620ab1e814630e155438f468c3ce47cf098a5d32757b8140821b528717
fof(binintersect_5FSubq_5F1,axiom,(! [X0] : (! [X1] : c_Subq(binintersect(X0,X1),X0)))). % ab22d20197cad203d5c9fe3d418292777f2d18e81c63de21cadf3e3a7810788b
fof(binintersect_5FSubq_5F2,axiom,(! [X0] : (! [X1] : c_Subq(binintersect(X0,X1),X1)))). % 1631379e768fcf9991063853f9d83e6639fd0a8eca9c6c6aecc03cd8b25a5d46
fof(binintersect_5FSubq_5Feq_5F1,axiom,(! [X0] : (! [X1] : (c_Subq(X0,X1) => (binintersect(X0,X1) = X0))))). % 9b8243c8d51df36232595bb6a54ef1efd7733b7e96b02b9faf1bf6ddb9cf204a
fof(binintersect_5FSubq_5Fmax,axiom,(! [X0] : (! [X1] : (! [X2] : (c_Subq(X2,X0) => (c_Subq(X2,X1) => c_Subq(X2,binintersect(X0,X1)))))))). % dc091d6184740a0ec73da1102fea8faf4bb3ffb9a908411cac31c0353a026173
fof(binintersect_5Fcom_5FSubq,axiom,(! [X0] : (! [X1] : c_Subq(binintersect(X0,X1),binintersect(X1,X0))))). % b04f1c0d7b7ab06346edf7b046833c6bd75692afd8136d6451229650cbfc8ab8
fof(binintersect_5Fcom,axiom,(! [X0] : (! [X1] : (binintersect(X0,X1) = binintersect(X1,X0))))). % 89b32b84af8e516fb5cde0f0ca143563535a8971e687e30a69e4ae28c8db1afb
fof(setminusI,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X0) => (nIn(X2,X1) => c_In(X2,setminus(X0,X1)))))))). % 8288e93b6088e201e20ca0b2b0b72fe9d40cba3051ebbe3f888bb9ae974f4ce7
fof(setminusE,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,setminus(X0,X1)) => (c_In(X2,X0) & nIn(X2,X1))))))). % 400e4bb15cd50b24f37f239fc7c0d228c3410893b31102399aa59d2ea875fb60
fof(setminusE1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,setminus(X0,X1)) => c_In(X2,X0)))))). % 8e1526a7d7bcb5f7eb8fc3a14a2d7fc79d0bc15338f8e4e8b21da538cba4cf64
fof(setminusE2,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,setminus(X0,X1)) => nIn(X2,X1)))))). % c8507f03e73a7f171961c01a49c0bec6f4a5ef95d09e5a1bc5a6aabcfbcae855
fof(setminus_5FSubq,axiom,(! [X0] : (! [X1] : c_Subq(setminus(X0,X1),X0)))). % 691304ddc6e76e363620558b1c9367048bde82b40c830ee183051e96f35ee022
fof(setminus_5FIn_5FPower,axiom,(! [X0] : (! [X1] : c_In(setminus(X0,X1),c_Power(X0))))). % 83b53c6e2122cffca9796caa4c5b1431d936e3b5694255b74ebc24a115abc75a
fof(binunion_5Fremove1_5Feq,axiom,(! [X0] : (! [X1] : (c_In(X1,X0) => (X0 = binunion(setminus(X0,c_Sing(X1)),c_Sing(X1))))))). % 296b1a8abc25c8b9087e3238156fab3ca312e7c26b6549b3378a98e1f1eaad1b
fof(c_In_5Firref,axiom,(! [X0] : nIn(X0,X0))). % 32d1b89792462a93a3f0b39fd0af65084fc19951789fbfedaf1434075442a3f9
fof(c_In_5Fno2cycle,axiom,(! [X0] : (! [X1] : (c_In(X0,X1) => (c_In(X1,X0) => $false))))). % 092f94151e13afcf352cc284da6b0c8dc39ee950c68abf2b8a08684a9649dca6
fof(ordsucc,axiom,(! [X0:$i] : (ordsucc(c_X0) = binunion(c_X0,c_Sing(c_X0))))). % 9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec
fof(ordsuccI1,axiom,(! [X0] : c_Subq(X0,ordsucc(X0)))). % 1d5d5b7b71ce4bb9a73edbf50070235dcc5bed8bf5dd7baab447bbd91db9807a
fof(ordsuccI2,axiom,(! [X0] : c_In(X0,ordsucc(X0)))). % 0bce99a2a196c1d6c6e5f195bcbe470674eab0f020f5c6768ba374f8363f164a
fof(ordsuccE,axiom,(! [X0] : (! [X1] : (c_In(X1,ordsucc(X0)) => (c_In(X1,X0) | (X1 = X0)))))). % 86defe2eaec7e0a7514339bd4f70688a0055e97b2bccbb0ea3ae8c06f32ce88a
fof(neq_5F0_5Fordsucc,axiom,(! [X0] : ~ (c_Empty = ordsucc(X0)))). % cd16045e375d4af84d5e4935492f9372af2c1df516250653f67f2eabce3e1a96
fof(neq_5Fordsucc_5F0,axiom,(! [X0] : ~ (ordsucc(X0) = c_Empty))). % 10d9661442ca65e01bc41935f4cb9aa6a33342df51d9e7dd2fd94e6c575e9dda
fof(ordsucc_5Finj,axiom,(! [X0] : (! [X1] : ((ordsucc(X0) = ordsucc(X1)) => (X0 = X1))))). % c0e03f00abde433cdda0dcc6cbe3d8c75fab364b4e5ec7433aeb6e1955558a49
fof(c_In_5F0_5F1,axiom,c_In(c_Empty,ordsucc(c_Empty))). % 4675abc9d31454cce6f27f63bfaacf6fc539a2b864cdd7bb9bf34598e85c9ff3
fof(c_In_5F0_5F2,axiom,c_In(c_Empty,ordsucc(ordsucc(c_Empty)))). % 4dcf737d976ab59871f178ab4227edffb26181c236613caeb68c84de8f2e6aa1
fof(c_In_5F1_5F2,axiom,c_In(ordsucc(c_Empty),ordsucc(ordsucc(c_Empty)))). % b28b8818076ea2727fe37ccdc19db7910186e7991e3cd809d9bd88239f294936
fof(nat_5F0,axiom,nat_5Fp(c_Empty)). % 8184e026ae720ae8ac54902d7e3149de08f2ad09a231d1695d0c97a705e1f859
fof(nat_5Fordsucc,axiom,(! [X0] : (nat_5Fp(X0) => nat_5Fp(ordsucc(X0))))). % c3f39850f8a787c21c048322f3dda0ed87723efae7899cefd3c49775f471b99b
fof(nat_5F1,axiom,nat_5Fp(ordsucc(c_Empty))). % a985fbd82807c603866f35d87f9d2827902df20043761c604b521c2cfc62c64e
fof(nat_5F2,axiom,nat_5Fp(ordsucc(ordsucc(c_Empty)))). % 28f0901270c9b9323f9278a82b158ea70a40f1d4ddfee5861486d22dc1bd7606
fof(nat_5F0_5Fin_5Fordsucc,axiom,(! [X0] : (nat_5Fp(X0) => c_In(c_Empty,ordsucc(X0))))). % cb67919398db6f11c2a4b410dd7fa5874724b7d2e2e1405849af78dca03a95bc
fof(nat_5Fordsucc_5Fin_5Fordsucc,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (c_In(X1,X0) => c_In(ordsucc(X1),ordsucc(X0))))))). % f2c2ec5ac5f1007b6100f9d8d698faba5c4a7de8b14e107578eca0163c7799c4
fof(nat_5Finv,axiom,(! [X0] : (nat_5Fp(X0) => ((X0 = c_Empty) | (? [X1] : (nat_5Fp(X1) & (X0 = ordsucc(X1)))))))). % 60e4d8db528b021fa7054c4e234c2b8f3ed4167b57341e3126724755a2dfd20c
fof(nat_5Fp_5Ftrans,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (c_In(X1,X0) => nat_5Fp(X1)))))). % 02c1be4fb7e8692a5ff13768a268b8f86936de1e79562d2d1c2a93838bee6cd2
fof(nat_5Ftrans,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (c_In(X1,X0) => c_Subq(X1,X0)))))). % ad6e9c68eaa15a57bb52641b049653bf19e99a0d8e5402cb7b6214d594de8561
fof(nat_5Fordsucc_5Ftrans,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (c_In(X1,ordsucc(X0)) => c_Subq(X1,X0)))))). % 28c5ca659f843c7e84c84347ea693e3888da4e8d9dceab0c3fff0d616d9c06cc
fof(atleastp_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : (atleastp(X0,X1) => (atleastp(X1,X2) => atleastp(X0,X2))))))). % a459514f533af0aa0f5c35dd114f33e34ae4d322e63c0410f91bf58d79ff13fe
fof(c_Subq_5Fatleastp,axiom,(! [X0] : (! [X1] : (c_Subq(X0,X1) => atleastp(X0,X1))))). % 877fe5b0cb6b8287108ca9aed1cdfdbc86e682215073795072a2da6e0d9db6b1
fof(equip_5Fatleastp,axiom,(! [X0] : (! [X1] : (equip(X0,X1) => atleastp(X0,X1))))). % 2ee17981b64518f1ca9743636c2c6c25551021a5c12b392c0f0351e7cfd3b6cd
fof(equip_5Fref,axiom,(! [X0] : equip(X0,X0))). % 71d8f2d93ec37cf4fa76487b6d2eb9d0410051bc927d2f35b2f987a884b7d002
fof(equip_5Fsym,axiom,(! [X0] : (! [X1] : (equip(X0,X1) => equip(X1,X0))))). % c07b874e6900f27e8a8737c2b8783387617c954dec4a46b9b3cc1cbaea9c6b37
fof(equip_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : (equip(X0,X1) => (equip(X1,X2) => equip(X0,X2))))))). % cb492df6d2d7489aa739f1c9ce70981c4c20fc2c8838171108a88b39af10e525
fof(equip_5F0_5FEmpty,axiom,(! [X0] : (equip(X0,c_Empty) => (X0 = c_Empty)))). % 2f0f69d51bec45a7b8f8d9a4907763107b173ff71c45a381664c7488ca7096bf
fof(equip_5Fadjoin_5Fordsucc,axiom,(! [X0] : (! [X1] : (! [X2] : (nIn(X2,X1) => (equip(X0,X1) => equip(ordsucc(X0),binunion(X1,c_Sing(X2))))))))). % 37a2e00564e7b2e38ac1de48eff4f00da7a08c692da0ce036bf8f04de888c32e
fof(equip_5Fordsucc_5Fremove1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X0) => (equip(X0,ordsucc(X1)) => equip(setminus(X0,c_Sing(X2)),X1))))))). % 019bf79338f95afa8d2c797734f29d7b4f36277e078b647e09c3fee4fb79f778
fof(setminus_5Fantimonotone,axiom,(! [X0] : (! [X1] : (! [X2] : (c_Subq(X1,X2) => c_Subq(setminus(X0,X2),setminus(X0,X1))))))). % f834915e222d99d9adaad0c8e862bc1384c10d3f4b9ce045b11fb075f120d5f3
fof(atleastp_5Fantisym_5Fequip,axiom,(! [X0] : (! [X1] : (atleastp(X0,X1) => (atleastp(X1,X0) => equip(X0,X1)))))). % 07130b13e2a320ff06b472a2707f24947179f2ecfa5a15e59205b817291fd2f8
fof(c_Pigeonhole_5Fnot_5Fatleastp_5Fordsucc,axiom,(! [X0] : (nat_5Fp(X0) => ~ atleastp(ordsucc(X0),X0)))). % c29d57653c9c5b2e351c04de5e8ef10584e9651a9247d5654d2f5c956ad51a77
fof(c_Union_5Fordsucc_5Feq,axiom,(! [X0] : (nat_5Fp(X0) => (c_Union(ordsucc(X0)) = X0)))). % 73f4179688eb6f1e9c80d6a1b13947b195e20a128e2e7dcbd7a7ca3d84a91857
fof(neq_5F0_5F1,axiom,~ (c_Empty = ordsucc(c_Empty))). % 2a012236fc59f277a006afea6589576917b98079dfa3b365b27050d0e9d91f80
fof(neq_5F1_5F0,axiom,~ (ordsucc(c_Empty) = c_Empty)). % a96636a83cef72bedda13177ba1f197ac6b6dab4613cc8062584e25c143b84fa
fof(neq_5F0_5F2,axiom,~ (c_Empty = ordsucc(ordsucc(c_Empty)))). % d7185afea09cc857260bbddd424bfd78941c0b9280cbff99a37a204ade989ef0
fof(conj_hammer_test_1122,conjecture,~ (ordsucc(ordsucc(c_Empty)) = c_Empty)).
