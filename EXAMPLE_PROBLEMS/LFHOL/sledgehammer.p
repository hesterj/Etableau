% TIMEFORMAT='%3R'; { time (exec 2>&1; /Users/blanchette/.isabelle/contrib/e-2.0-2/x86_64-darwin/eprover --auto-schedule --tstp-in --tstp-out --silent --cpu-limit=2 --proof-object=1 /Users/blanchette/hgs/matryoshka/papers/2019-TACAS-ehoh/eval/judgment_day/judgment_day_lifting_32/arr/prob_224__3924992_1 ) ; }
% This file was generated by Isabelle (most likely Sledgehammer)
% 2018-05-22 19:05:29.117

% Could-be-implicit typings (7)
thf(ty_n_t__Set__Oset_I_062_It__Arrow____Order____Mirabelle____lmkjsnsgsd__Oindi_Mt__Set__Oset_It__Product____Type__Oprod_It__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_Mt__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_J_J_J_J, type,
    set_Ar1010370258le_alt : $tType).
thf(ty_n_t__Set__Oset_It__Set__Oset_It__Product____Type__Oprod_It__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_Mt__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_J_J_J, type,
    set_se994205567le_alt : $tType).
thf(ty_n_t__Set__Oset_It__Product____Type__Oprod_It__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_Mt__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_J_J, type,
    set_Pr650783177le_alt : $tType).
thf(ty_n_t__Product____Type__Oprod_It__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_Mt__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_J, type,
    produc1240157459le_alt : $tType).
thf(ty_n_t__Arrow____Order____Mirabelle____lmkjsnsgsd__Oindi, type,
    arrow_1277843352e_indi : $tType).
thf(ty_n_t__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt, type,
    arrow_1970237595le_alt : $tType).
thf(ty_n_t__HOL__Obool, type,
    bool : $tType).

% Explicit typings (29)
thf(sy_c_ATP_058Lamm__a____, type,
    aTP_Lamm_a : arrow_1277843352e_indi > set_Pr650783177le_alt).
thf(sy_c_ATP_058Lamm__aa____, type,
    aTP_Lamm_aa : arrow_1277843352e_indi > set_Pr650783177le_alt).
thf(sy_c_ATP_058Lamm__ab____, type,
    aTP_Lamm_ab : arrow_1277843352e_indi > set_Pr650783177le_alt).
thf(sy_c_ATP_058Lamm__ac____, type,
    aTP_Lamm_ac : set_Pr650783177le_alt > produc1240157459le_alt > bool).
thf(sy_c_ATP_058Lamm__ad____, type,
    aTP_Lamm_ad : set_Ar1010370258le_alt > (arrow_1277843352e_indi > set_Pr650783177le_alt) > bool).
thf(sy_c_ATP_058Lamm__ae____, type,
    aTP_Lamm_ae : set_se994205567le_alt > set_Pr650783177le_alt > bool).
thf(sy_c_Arrow__Order__Mirabelle__lmkjsnsgsd_OIIA, type,
    arrow_993220427le_IIA : ((arrow_1277843352e_indi > set_Pr650783177le_alt) > set_Pr650783177le_alt) > bool).
thf(sy_c_Arrow__Order__Mirabelle__lmkjsnsgsd_OLin, type,
    arrow_1020104155le_Lin : set_se994205567le_alt).
thf(sy_c_Arrow__Order__Mirabelle__lmkjsnsgsd_OProf, type,
    arrow_1123792911e_Prof : set_Ar1010370258le_alt).
thf(sy_c_Arrow__Order__Mirabelle__lmkjsnsgsd_Obelow, type,
    arrow_475411515_below : set_Pr650783177le_alt > arrow_1970237595le_alt > arrow_1970237595le_alt > set_Pr650783177le_alt).
thf(sy_c_Arrow__Order__Mirabelle__lmkjsnsgsd_Omkbot, type,
    arrow_431657651_mkbot : set_Pr650783177le_alt > arrow_1970237595le_alt > set_Pr650783177le_alt).
thf(sy_c_Arrow__Order__Mirabelle__lmkjsnsgsd_Omktop, type,
    arrow_580364737_mktop : set_Pr650783177le_alt > arrow_1970237595le_alt > set_Pr650783177le_alt).
thf(sy_c_Arrow__Order__Mirabelle__lmkjsnsgsd_Ounanimity, type,
    arrow_440531566nimity : ((arrow_1277843352e_indi > set_Pr650783177le_alt) > set_Pr650783177le_alt) > bool).
thf(sy_c_Product__Type_OPair_001t__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_001t__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt, type,
    produc1584245005le_alt : arrow_1970237595le_alt > arrow_1970237595le_alt > produc1240157459le_alt).
thf(sy_c_Set_OCollect_001_062_It__Arrow____Order____Mirabelle____lmkjsnsgsd__Oindi_Mt__Set__Oset_It__Product____Type__Oprod_It__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_Mt__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_J_J_J, type,
    collec344444381le_alt : ((arrow_1277843352e_indi > set_Pr650783177le_alt) > bool) > set_Ar1010370258le_alt).
thf(sy_c_Set_OCollect_001t__Product____Type__Oprod_It__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_Mt__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_J, type,
    collec1755567720le_alt : (produc1240157459le_alt > bool) > set_Pr650783177le_alt).
thf(sy_c_Set_OCollect_001t__Set__Oset_It__Product____Type__Oprod_It__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_Mt__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_J_J, type,
    collec1682628382le_alt : (set_Pr650783177le_alt > bool) > set_se994205567le_alt).
thf(sy_c_fFalse, type,
    fFalse : bool).
thf(sy_c_fTrue, type,
    fTrue : bool).
thf(sy_c_member_001_062_It__Arrow____Order____Mirabelle____lmkjsnsgsd__Oindi_Mt__Set__Oset_It__Product____Type__Oprod_It__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_Mt__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_J_J_J, type,
    member1617113243le_alt : (arrow_1277843352e_indi > set_Pr650783177le_alt) > set_Ar1010370258le_alt > bool).
thf(sy_c_member_001t__Product____Type__Oprod_It__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_Mt__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_J, type,
    member1124141610le_alt : produc1240157459le_alt > set_Pr650783177le_alt > bool).
thf(sy_c_member_001t__Set__Oset_It__Product____Type__Oprod_It__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_Mt__Arrow____Order____Mirabelle____lmkjsnsgsd__Oalt_J_J, type,
    member1617431264le_alt : set_Pr650783177le_alt > set_se994205567le_alt > bool).
thf(sy_c_pp, type,
    pp : bool > $o).
thf(sy_v_F, type,
    f : (arrow_1277843352e_indi > set_Pr650783177le_alt) > set_Pr650783177le_alt).
thf(sy_v_P_H____, type,
    p : arrow_1277843352e_indi > set_Pr650783177le_alt).
thf(sy_v_P____, type,
    p2 : arrow_1277843352e_indi > set_Pr650783177le_alt).
thf(sy_v_a____, type,
    a : arrow_1970237595le_alt).
thf(sy_v_b____, type,
    b : arrow_1970237595le_alt).
thf(sy_v_c____, type,
    c : arrow_1970237595le_alt).

% Relevant facts (43)
thf(fact_0__092_060open_062P_H_A_092_060in_062_AProf_092_060close_062, axiom,
    ((pp @ (member1617113243le_alt @ p @ arrow_1123792911e_Prof)))). % \<open>P' \<in> Prof\<close>
thf(fact_1__092_060open_062P_A_092_060in_062_AProf_092_060close_062, axiom,
    ((pp @ (member1617113243le_alt @ p2 @ arrow_1123792911e_Prof)))). % \<open>P \<in> Prof\<close>
thf(fact_2_assms_I3_J, axiom,
    ((pp @ (arrow_993220427le_IIA @ f)))). % assms(3)
thf(fact_3_u, axiom,
    ((pp @ (arrow_440531566nimity @ f)))). % u
thf(fact_4__092_060open_062a_A_092_060noteq_062_Ab_092_060close_062, axiom,
    ((~ ((a = b))))). % \<open>a \<noteq> b\<close>
thf(fact_5__092_060open_062_I_092_060lambda_062p_O_Abelow_A_Ibelow_A_Ibelow_A_IP_Ap_J_Ac_Ab_J_Ab_Aa_J_Aa_Ac_J_A_092_060in_062_AProf_092_060close_062, axiom,
    ((pp @ (member1617113243le_alt @ aTP_Lamm_a @ arrow_1123792911e_Prof)))). % \<open>(\<lambda>p. below (below (below (P p) c b) b a) a c) \<in> Prof\<close>
thf(fact_6__092_060open_062_092_060forall_062i_O_A_Ib_A_060_092_060_094bsub_062below_A_Ibelow_A_Ibelow_A_IP_Ai_J_Ac_Ab_J_Ab_Aa_J_Aa_Ac_092_060_094esub_062_Aa_J_A_061_A_Ib_A_060_092_060_094bsub_062P_H_Ai_092_060_094esub_062_Aa_J_092_060close_062, axiom,
    ((![I : arrow_1277843352e_indi]: ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ b @ a) @ (arrow_475411515_below @ (arrow_475411515_below @ (arrow_475411515_below @ (p2 @ I) @ c @ b) @ b @ a) @ a @ c))) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ b @ a) @ (p @ I))))))). % \<open>\<forall>i. (b <\<^bsub>below (below (below (P i) c b) b a) a c\<^esub> a) = (b <\<^bsub>P' i\<^esub> a)\<close>
thf(fact_7__C1_C, axiom,
    ((![A : arrow_1970237595le_alt, B : arrow_1970237595le_alt, A2 : arrow_1970237595le_alt, B2 : arrow_1970237595le_alt, P : arrow_1277843352e_indi > set_Pr650783177le_alt, P2 : arrow_1277843352e_indi > set_Pr650783177le_alt]: ((~ ((A = B))) => ((~ ((A2 = B2))) => ((~ ((A = B2))) => ((~ ((B = A2))) => ((pp @ (member1617113243le_alt @ P @ arrow_1123792911e_Prof)) => ((pp @ (member1617113243le_alt @ P2 @ arrow_1123792911e_Prof)) => ((![I2 : arrow_1277843352e_indi]: ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ A @ B) @ (P @ I2))) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ A2 @ B2) @ (P2 @ I2))))) => ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ A @ B) @ (f @ P))) => (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ A2 @ B2) @ (f @ P2)))))))))))))). % "1"
thf(fact_8__C2_C, axiom,
    ((![A : arrow_1970237595le_alt, B : arrow_1970237595le_alt, A2 : arrow_1970237595le_alt, B2 : arrow_1970237595le_alt, P : arrow_1277843352e_indi > set_Pr650783177le_alt, P2 : arrow_1277843352e_indi > set_Pr650783177le_alt]: ((~ ((A = B))) => ((~ ((A2 = B2))) => ((~ ((A = B2))) => ((~ ((B = A2))) => ((pp @ (member1617113243le_alt @ P @ arrow_1123792911e_Prof)) => ((pp @ (member1617113243le_alt @ P2 @ arrow_1123792911e_Prof)) => ((![I2 : arrow_1277843352e_indi]: ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ A @ B) @ (P @ I2))) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ A2 @ B2) @ (P2 @ I2))))) => ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ A @ B) @ (f @ P))) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ A2 @ B2) @ (f @ P2)))))))))))))). % "2"
thf(fact_9_iff, axiom,
    ((![I : arrow_1277843352e_indi]: ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ a @ b) @ (p2 @ I))) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ b @ a) @ (p @ I))))))). % iff
thf(fact_10__092_060open_062_092_060forall_062i_O_A_Ia_A_060_092_060_094bsub_062P_Ai_092_060_094esub_062_Ab_J_A_061_A_Ia_A_060_092_060_094bsub_062below_A_IP_Ai_J_Ac_Ab_092_060_094esub_062_Ac_J_092_060close_062, axiom,
    ((![I : arrow_1277843352e_indi]: ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ a @ b) @ (p2 @ I))) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ a @ c) @ (arrow_475411515_below @ (p2 @ I) @ c @ b))))))). % \<open>\<forall>i. (a <\<^bsub>P i\<^esub> b) = (a <\<^bsub>below (P i) c b\<^esub> c)\<close>
thf(fact_11__092_060open_062_092_060forall_062i_O_A_Ia_A_060_092_060_094bsub_062below_A_IP_Ai_J_Ac_Ab_092_060_094esub_062_Ac_J_A_061_A_Ib_A_060_092_060_094bsub_062below_A_Ibelow_A_IP_Ai_J_Ac_Ab_J_Ab_Aa_092_060_094esub_062_Ac_J_092_060close_062, axiom,
    ((![I : arrow_1277843352e_indi]: ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ a @ c) @ (arrow_475411515_below @ (p2 @ I) @ c @ b))) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ b @ c) @ (arrow_475411515_below @ (arrow_475411515_below @ (p2 @ I) @ c @ b) @ b @ a))))))). % \<open>\<forall>i. (a <\<^bsub>below (P i) c b\<^esub> c) = (b <\<^bsub>below (below (P i) c b) b a\<^esub> c)\<close>
thf(fact_12__092_060open_062_092_060forall_062i_O_A_Ib_A_060_092_060_094bsub_062below_A_Ibelow_A_Ibelow_A_IP_Ai_J_Ac_Ab_J_Ab_Aa_J_Aa_Ac_092_060_094esub_062_Aa_J_A_061_A_Ia_A_060_092_060_094bsub_062P_Ai_092_060_094esub_062_Ab_J_092_060close_062, axiom,
    ((![I : arrow_1277843352e_indi]: ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ b @ a) @ (arrow_475411515_below @ (arrow_475411515_below @ (arrow_475411515_below @ (p2 @ I) @ c @ b) @ b @ a) @ a @ c))) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ a @ b) @ (p2 @ I))))))). % \<open>\<forall>i. (b <\<^bsub>below (below (below (P i) c b) b a) a c\<^esub> a) = (a <\<^bsub>P i\<^esub> b)\<close>
thf(fact_13__092_060open_062_092_060forall_062i_O_A_Ib_A_060_092_060_094bsub_062below_A_Ibelow_A_IP_Ai_J_Ac_Ab_J_Ab_Aa_092_060_094esub_062_Ac_J_A_061_A_Ib_A_060_092_060_094bsub_062below_A_Ibelow_A_Ibelow_A_IP_Ai_J_Ac_Ab_J_Ab_Aa_J_Aa_Ac_092_060_094esub_062_Aa_J_092_060close_062, axiom,
    ((![I : arrow_1277843352e_indi]: ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ b @ c) @ (arrow_475411515_below @ (arrow_475411515_below @ (p2 @ I) @ c @ b) @ b @ a))) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ b @ a) @ (arrow_475411515_below @ (arrow_475411515_below @ (arrow_475411515_below @ (p2 @ I) @ c @ b) @ b @ a) @ a @ c))))))). % \<open>\<forall>i. (b <\<^bsub>below (below (P i) c b) b a\<^esub> c) = (b <\<^bsub>below (below (below (P i) c b) b a) a c\<^esub> a)\<close>
thf(fact_14__092_060open_062_I_092_060lambda_062p_O_Abelow_A_IP_Ap_J_Ac_Ab_J_A_092_060in_062_AProf_092_060close_062, axiom,
    ((pp @ (member1617113243le_alt @ aTP_Lamm_aa @ arrow_1123792911e_Prof)))). % \<open>(\<lambda>p. below (P p) c b) \<in> Prof\<close>
thf(fact_15_ab, axiom,
    (((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ a @ b) @ (f @ p2))) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ a @ c) @ (f @ aTP_Lamm_aa)))))). % ab
thf(fact_16_ac, axiom,
    (((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ a @ c) @ (f @ aTP_Lamm_aa))) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ b @ c) @ (f @ aTP_Lamm_ab)))))). % ac
thf(fact_17_bc, axiom,
    (((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ b @ c) @ (f @ aTP_Lamm_ab))) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ b @ a) @ (f @ aTP_Lamm_a)))))). % bc
thf(fact_18__092_060open_062_I_092_060lambda_062p_O_Abelow_A_Ibelow_A_IP_Ap_J_Ac_Ab_J_Ab_Aa_J_A_092_060in_062_AProf_092_060close_062, axiom,
    ((pp @ (member1617113243le_alt @ aTP_Lamm_ab @ arrow_1123792911e_Prof)))). % \<open>(\<lambda>p. below (below (P p) c b) b a) \<in> Prof\<close>
thf(fact_19_prod_Oinject, axiom,
    ((![X1 : arrow_1970237595le_alt, X2 : arrow_1970237595le_alt, Y1 : arrow_1970237595le_alt, Y2 : arrow_1970237595le_alt]: (((produc1584245005le_alt @ X1 @ X2) = (produc1584245005le_alt @ Y1 @ Y2)) <=> ((X1 = Y1) & (X2 = Y2)))))). % prod.inject
thf(fact_20_old_Oprod_Oinject, axiom,
    ((![A : arrow_1970237595le_alt, B : arrow_1970237595le_alt, A2 : arrow_1970237595le_alt, B2 : arrow_1970237595le_alt]: (((produc1584245005le_alt @ A @ B) = (produc1584245005le_alt @ A2 @ B2)) <=> ((A = A2) & (B = B2)))))). % old.prod.inject
thf(fact_21_pred__equals__eq2, axiom,
    ((![R : set_Pr650783177le_alt, S : set_Pr650783177le_alt]: ((![X : arrow_1970237595le_alt, Xa : arrow_1970237595le_alt]: ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ X @ Xa) @ R)) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ X @ Xa) @ S)))) <=> (R = S))))). % pred_equals_eq2
thf(fact_22_in__mkbot, axiom,
    ((![X3 : arrow_1970237595le_alt, Y : arrow_1970237595le_alt, L : set_Pr650783177le_alt, Z : arrow_1970237595le_alt]: ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ X3 @ Y) @ (arrow_431657651_mkbot @ L @ Z))) <=> ((~ ((Y = Z))) & (((X3 = Z) => (~ ((X3 = Y)))) & ((~ ((X3 = Z))) => (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ X3 @ Y) @ L))))))))). % in_mkbot
thf(fact_23_in__mktop, axiom,
    ((![X3 : arrow_1970237595le_alt, Y : arrow_1970237595le_alt, L : set_Pr650783177le_alt, Z : arrow_1970237595le_alt]: ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ X3 @ Y) @ (arrow_580364737_mktop @ L @ Z))) <=> ((~ ((X3 = Z))) & (((Y = Z) => (~ ((X3 = Y)))) & ((~ ((Y = Z))) => (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ X3 @ Y) @ L))))))))). % in_mktop
thf(fact_24_in__below, axiom,
    ((![A : arrow_1970237595le_alt, B : arrow_1970237595le_alt, L : set_Pr650783177le_alt, X3 : arrow_1970237595le_alt, Y : arrow_1970237595le_alt]: ((~ ((A = B))) => ((pp @ (member1617431264le_alt @ L @ arrow_1020104155le_Lin)) => ((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ X3 @ Y) @ (arrow_475411515_below @ L @ A @ B))) <=> ((~ ((X3 = Y))) & (((Y = A) => (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ X3 @ B) @ L))) & ((~ ((Y = A))) => (((X3 = A) => ((Y = B) | (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ B @ Y) @ L)))) & ((~ ((X3 = A))) => (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ X3 @ Y) @ L))))))))))))). % in_below
thf(fact_25_surj__pair, axiom,
    ((![P3 : produc1240157459le_alt]: (?[X4 : arrow_1970237595le_alt, Y3 : arrow_1970237595le_alt]: (P3 = (produc1584245005le_alt @ X4 @ Y3)))))). % surj_pair
thf(fact_26_prod__cases, axiom,
    ((![P : produc1240157459le_alt > bool, P3 : produc1240157459le_alt]: ((![A3 : arrow_1970237595le_alt, B3 : arrow_1970237595le_alt]: (pp @ (P @ (produc1584245005le_alt @ A3 @ B3)))) => (pp @ (P @ P3)))))). % prod_cases
thf(fact_27_Pair__inject, axiom,
    ((![A : arrow_1970237595le_alt, B : arrow_1970237595le_alt, A2 : arrow_1970237595le_alt, B2 : arrow_1970237595le_alt]: (((produc1584245005le_alt @ A @ B) = (produc1584245005le_alt @ A2 @ B2)) => (~ (((A = A2) => (~ ((B = B2)))))))))). % Pair_inject
thf(fact_28_mem__Collect__eq, axiom,
    ((![A : produc1240157459le_alt, P : produc1240157459le_alt > bool]: ((pp @ (member1124141610le_alt @ A @ (collec1755567720le_alt @ P))) <=> (pp @ (P @ A)))))). % mem_Collect_eq
thf(fact_29_mem__Collect__eq, axiom,
    ((![A : arrow_1277843352e_indi > set_Pr650783177le_alt, P : (arrow_1277843352e_indi > set_Pr650783177le_alt) > bool]: ((pp @ (member1617113243le_alt @ A @ (collec344444381le_alt @ P))) <=> (pp @ (P @ A)))))). % mem_Collect_eq
thf(fact_30_mem__Collect__eq, axiom,
    ((![A : set_Pr650783177le_alt, P : set_Pr650783177le_alt > bool]: ((pp @ (member1617431264le_alt @ A @ (collec1682628382le_alt @ P))) <=> (pp @ (P @ A)))))). % mem_Collect_eq
thf(fact_31_Collect__mem__eq, axiom,
    ((![A4 : set_Pr650783177le_alt]: ((collec1755567720le_alt @ (aTP_Lamm_ac @ A4)) = A4)))). % Collect_mem_eq
thf(fact_32_Collect__mem__eq, axiom,
    ((![A4 : set_Ar1010370258le_alt]: ((collec344444381le_alt @ (aTP_Lamm_ad @ A4)) = A4)))). % Collect_mem_eq
thf(fact_33_Collect__mem__eq, axiom,
    ((![A4 : set_se994205567le_alt]: ((collec1682628382le_alt @ (aTP_Lamm_ae @ A4)) = A4)))). % Collect_mem_eq
thf(fact_34_Collect__cong, axiom,
    ((![P : set_Pr650783177le_alt > bool, Q : set_Pr650783177le_alt > bool]: ((![X4 : set_Pr650783177le_alt]: ((pp @ (P @ X4)) <=> (pp @ (Q @ X4)))) => ((collec1682628382le_alt @ P) = (collec1682628382le_alt @ Q)))))). % Collect_cong
thf(fact_35_Collect__cong, axiom,
    ((![P : (arrow_1277843352e_indi > set_Pr650783177le_alt) > bool, Q : (arrow_1277843352e_indi > set_Pr650783177le_alt) > bool]: ((![X4 : arrow_1277843352e_indi > set_Pr650783177le_alt]: ((pp @ (P @ X4)) <=> (pp @ (Q @ X4)))) => ((collec344444381le_alt @ P) = (collec344444381le_alt @ Q)))))). % Collect_cong
thf(fact_36_Collect__cong, axiom,
    ((![P : produc1240157459le_alt > bool, Q : produc1240157459le_alt > bool]: ((![X4 : produc1240157459le_alt]: ((pp @ (P @ X4)) <=> (pp @ (Q @ X4)))) => ((collec1755567720le_alt @ P) = (collec1755567720le_alt @ Q)))))). % Collect_cong
thf(fact_37_ATP_Olambda__1, axiom,
    ((![Uu : arrow_1277843352e_indi]: ((aTP_Lamm_a @ Uu) = (arrow_475411515_below @ (arrow_475411515_below @ (arrow_475411515_below @ (p2 @ Uu) @ c @ b) @ b @ a) @ a @ c))))). % ATP.lambda_1
thf(fact_38_ATP_Olambda__2, axiom,
    ((![Uu : arrow_1277843352e_indi]: ((aTP_Lamm_ab @ Uu) = (arrow_475411515_below @ (arrow_475411515_below @ (p2 @ Uu) @ c @ b) @ b @ a))))). % ATP.lambda_2
thf(fact_39_ATP_Olambda__3, axiom,
    ((![Uu : arrow_1277843352e_indi]: ((aTP_Lamm_aa @ Uu) = (arrow_475411515_below @ (p2 @ Uu) @ c @ b))))). % ATP.lambda_3
thf(fact_40_ATP_Olambda__4, axiom,
    ((![Uu : set_Pr650783177le_alt, Uua : produc1240157459le_alt]: ((pp @ (aTP_Lamm_ac @ Uu @ Uua)) <=> (pp @ (member1124141610le_alt @ Uua @ Uu)))))). % ATP.lambda_4
thf(fact_41_ATP_Olambda__5, axiom,
    ((![Uu : set_se994205567le_alt, Uua : set_Pr650783177le_alt]: ((pp @ (aTP_Lamm_ae @ Uu @ Uua)) <=> (pp @ (member1617431264le_alt @ Uua @ Uu)))))). % ATP.lambda_5
thf(fact_42_ATP_Olambda__6, axiom,
    ((![Uu : set_Ar1010370258le_alt, Uua : arrow_1277843352e_indi > set_Pr650783177le_alt]: ((pp @ (aTP_Lamm_ad @ Uu @ Uua)) <=> (pp @ (member1617113243le_alt @ Uua @ Uu)))))). % ATP.lambda_6

% Helper facts (2)
thf(help_pp_2_1_U, axiom,
    ((pp @ fTrue))).
thf(help_pp_1_1_U, axiom,
    ((~ ((pp @ fFalse))))).

% Conjectures (1)
thf(conj_0, conjecture,
    (((pp @ (member1124141610le_alt @ (produc1584245005le_alt @ b @ a) @ (f @ aTP_Lamm_a))) <=> (pp @ (member1124141610le_alt @ (produc1584245005le_alt @ b @ a) @ (f @ p)))))).