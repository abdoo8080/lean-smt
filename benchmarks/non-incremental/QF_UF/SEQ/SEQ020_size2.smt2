(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
CADE ATP System competition. See http://www.cs.miami.edu/~tptp/CASC
 for more information. 

This benchmark was obtained by trying to find a finite model of a first-order 
formula (Albert Oliveras).
|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort U 0)
(declare-fun p3 (U) Bool)
(declare-fun p1 (U U) Bool)
(declare-fun p4 (U) Bool)
(declare-fun p14 (U U U) Bool)
(declare-fun p9 (U) Bool)
(declare-fun f12 (U) U)
(declare-fun f6 (U) U)
(declare-fun f2 (U U) U)
(declare-fun f17 (U U U) U)
(declare-fun p10 (U U) Bool)
(declare-fun f16 (U U U) U)
(declare-fun f7 (U) U)
(declare-fun f13 (U U U) U)
(declare-fun c18 () U)
(declare-fun f11 (U) U)
(declare-fun f5 (U) U)
(declare-fun c8 () U)
(declare-fun p15 (U U) Bool)
(declare-fun c_0 () U)
(declare-fun c_1 () U)
(assert (let ((?v_1 (not (p3 c_0))) (?v_0 (p1 c_0 c_0))) (let ((?v_3 (not ?v_0)) (?v_2 (= c_0 c_0)) (?v_5 (not (p4 c_0))) (?v_28 (p14 c_0 c_0 c_0))) (let ((?v_8 (not ?v_28)) (?v_4 (= c_0 c_1)) (?v_12 (p1 c_1 c_0)) (?v_9 (not (p3 c_1))) (?v_30 (p14 c_0 c_0 c_1))) (let ((?v_11 (not ?v_30)) (?v_6 (p1 c_0 c_1))) (let ((?v_7 (not ?v_6)) (?v_10 (not (p4 c_1))) (?v_15 (p1 c_1 c_1)) (?v_14 (not ?v_12)) (?v_13 (= c_1 c_0)) (?v_32 (p14 c_1 c_0 c_0))) (let ((?v_16 (not ?v_32)) (?v_18 (= c_1 c_1)) (?v_34 (p14 c_1 c_0 c_1))) (let ((?v_19 (not ?v_34)) (?v_17 (not ?v_15)) (?v_29 (p14 c_0 c_1 c_0))) (let ((?v_20 (not ?v_29)) (?v_31 (p14 c_0 c_1 c_1))) (let ((?v_21 (not ?v_31)) (?v_33 (p14 c_1 c_1 c_0))) (let ((?v_22 (not ?v_33)) (?v_35 (p14 c_1 c_1 c_1))) (let ((?v_23 (not ?v_35)) (?v_36 (not (p9 c_0))) (?v_102 (f12 c_0)) (?v_38 (not (p9 c_1))) (?v_103 (f12 c_1)) (?v_61 (f6 c_0)) (?v_63 (f6 c_1)) (?v_24 (f2 c_0 c_0)) (?v_25 (f2 c_0 c_1)) (?v_26 (f2 c_1 c_0)) (?v_27 (f2 c_1 c_1))) (let ((?v_84 (p1 c_0 ?v_24)) (?v_85 (p1 c_1 ?v_27)) (?v_64 (f17 c_0 c_0 c_0)) (?v_68 (f17 c_0 c_1 c_0)) (?v_66 (f17 c_0 c_0 c_1)) (?v_70 (f17 c_0 c_1 c_1)) (?v_65 (f17 c_1 c_0 c_0)) (?v_69 (f17 c_1 c_1 c_0)) (?v_67 (f17 c_1 c_0 c_1)) (?v_71 (f17 c_1 c_1 c_1)) (?v_37 (not (p10 c_0 c_0))) (?v_52 (f16 c_0 c_0 c_0)) (?v_40 (not (p10 c_0 c_1))) (?v_54 (f16 c_0 c_1 c_0)) (?v_39 (not (p10 c_1 c_0))) (?v_56 (f16 c_0 c_0 c_1)) (?v_41 (not (p10 c_1 c_1))) (?v_58 (f16 c_0 c_1 c_1)) (?v_53 (f16 c_1 c_0 c_0)) (?v_55 (f16 c_1 c_1 c_0)) (?v_57 (f16 c_1 c_0 c_1)) (?v_59 (f16 c_1 c_1 c_1)) (?v_94 (f7 c_0)) (?v_95 (f7 c_1)) (?v_72 (f13 c_0 c_0 c_0))) (let ((?v_42 (p10 c_0 ?v_72)) (?v_43 (f13 c_1 c_0 c_0)) (?v_73 (f13 c_0 c_1 c_0))) (let ((?v_46 (p10 c_0 ?v_73)) (?v_47 (f13 c_1 c_1 c_0))) (let ((?v_93 (p10 c_1 ?v_47)) (?v_44 (f13 c_0 c_0 c_1))) (let ((?v_90 (p10 c_0 ?v_44)) (?v_74 (f13 c_1 c_0 c_1))) (let ((?v_45 (p10 c_1 ?v_74)) (?v_48 (f13 c_0 c_1 c_1)) (?v_75 (f13 c_1 c_1 c_1))) (let ((?v_49 (p10 c_1 ?v_75)) (?v_92 (p10 c_0 ?v_43)) (?v_91 (p10 c_1 ?v_48)) (?v_50 (not (p10 c_0 c18))) (?v_51 (not (p10 c_1 c18))) (?v_100 (f11 c_0)) (?v_101 (f11 c_1)) (?v_60 (f5 c_0)) (?v_62 (f5 c_1)) (?v_80 (p10 ?v_52 c_0)) (?v_81 (p10 ?v_55 c_1)) (?v_82 (p10 ?v_56 c_0)) (?v_83 (p10 ?v_59 c_1)) (?v_76 (p1 c_0 ?v_64)) (?v_77 (p1 c_0 ?v_65)) (?v_86 (p1 c_0 ?v_66)) (?v_89 (p1 c_1 ?v_69)) (?v_78 (p1 c_1 ?v_70)) (?v_79 (p1 c_1 ?v_71)) (?v_88 (p1 c_0 ?v_68)) (?v_87 (p1 c_1 ?v_67)) (?v_96 (p15 c_0 c_0)) (?v_97 (p15 c_1 c_0)) (?v_98 (p15 c_0 c_1)) (?v_99 (p15 c_1 c_1))) (and (distinct c_0 c_1) (or ?v_1 ?v_3 ?v_2 ?v_0 ?v_1 ?v_1 ?v_2 ?v_3 ?v_5 ?v_2 ?v_8) (or ?v_1 ?v_3 ?v_4 ?v_12 ?v_1 ?v_9 ?v_4 ?v_3 ?v_5 ?v_2 ?v_11) (or ?v_1 ?v_7 ?v_2 ?v_6 ?v_1 ?v_1 ?v_2 ?v_7 ?v_10 ?v_2 ?v_8) (or ?v_1 ?v_7 ?v_4 ?v_15 ?v_1 ?v_9 ?v_4 ?v_7 ?v_10 ?v_2 ?v_11) (or ?v_1 ?v_14 ?v_13 ?v_0 ?v_9 ?v_1 ?v_2 ?v_3 ?v_5 ?v_13 ?v_16) (or ?v_1 ?v_14 ?v_18 ?v_12 ?v_9 ?v_9 ?v_4 ?v_3 ?v_5 ?v_13 ?v_19) (or ?v_1 ?v_17 ?v_13 ?v_6 ?v_9 ?v_1 ?v_2 ?v_7 ?v_10 ?v_13 ?v_16) (or ?v_1 ?v_17 ?v_18 ?v_15 ?v_9 ?v_9 ?v_4 ?v_7 ?v_10 ?v_13 ?v_19) (or ?v_9 ?v_3 ?v_2 ?v_0 ?v_1 ?v_1 ?v_13 ?v_14 ?v_5 ?v_4 ?v_20) (or ?v_9 ?v_3 ?v_4 ?v_12 ?v_1 ?v_9 ?v_18 ?v_14 ?v_5 ?v_4 ?v_21) (or ?v_9 ?v_7 ?v_2 ?v_6 ?v_1 ?v_1 ?v_13 ?v_17 ?v_10 ?v_4 ?v_20) (or ?v_9 ?v_7 ?v_4 ?v_15 ?v_1 ?v_9 ?v_18 ?v_17 ?v_10 ?v_4 ?v_21) (or ?v_9 ?v_14 ?v_13 ?v_0 ?v_9 ?v_1 ?v_13 ?v_14 ?v_5 ?v_18 ?v_22) (or ?v_9 ?v_14 ?v_18 ?v_12 ?v_9 ?v_9 ?v_18 ?v_14 ?v_5 ?v_18 ?v_23) (or ?v_9 ?v_17 ?v_13 ?v_6 ?v_9 ?v_1 ?v_13 ?v_17 ?v_10 ?v_18 ?v_22) (or ?v_9 ?v_17 ?v_18 ?v_15 ?v_9 ?v_9 ?v_18 ?v_17 ?v_10 ?v_18 ?v_23) (or ?v_36 (p3 ?v_102)) (or ?v_38 (p3 ?v_103)) (or ?v_5 (p1 ?v_61 c_0)) (or ?v_10 (p1 ?v_63 c_1)) (or ?v_1 (p4 ?v_24) ?v_2 ?v_1) (or ?v_1 (p4 ?v_25) ?v_4 ?v_9) (or ?v_9 (p4 ?v_26) ?v_13 ?v_1) (or ?v_9 (p4 ?v_27) ?v_18 ?v_9) (or ?v_5 ?v_1 ?v_2 ?v_1 ?v_2 ?v_3 ?v_3 ?v_3 ?v_5 ?v_3) (or ?v_5 ?v_1 ?v_2 ?v_9 ?v_4 ?v_14 ?v_3 ?v_14 ?v_5 ?v_3) (or ?v_5 ?v_1 ?v_13 ?v_1 ?v_2 ?v_3 ?v_7 ?v_7 ?v_10 ?v_3) (or ?v_5 ?v_1 ?v_13 ?v_9 ?v_4 ?v_14 ?v_7 ?v_17 ?v_10 ?v_3) (or ?v_5 ?v_9 ?v_2 ?v_1 ?v_13 ?v_3 ?v_14 ?v_3 ?v_5 ?v_14) (or ?v_5 ?v_9 ?v_2 ?v_9 ?v_18 ?v_14 ?v_14 ?v_14 ?v_5 ?v_14) (or ?v_5 ?v_9 ?v_13 ?v_1 ?v_13 ?v_3 ?v_17 ?v_7 ?v_10 ?v_14) (or ?v_5 ?v_9 ?v_13 ?v_9 ?v_18 ?v_14 ?v_17 ?v_17 ?v_10 ?v_14) (or ?v_10 ?v_1 ?v_4 ?v_1 ?v_2 ?v_7 ?v_3 ?v_3 ?v_5 ?v_7) (or ?v_10 ?v_1 ?v_4 ?v_9 ?v_4 ?v_17 ?v_3 ?v_14 ?v_5 ?v_7) (or ?v_10 ?v_1 ?v_18 ?v_1 ?v_2 ?v_7 ?v_7 ?v_7 ?v_10 ?v_7) (or ?v_10 ?v_1 ?v_18 ?v_9 ?v_4 ?v_17 ?v_7 ?v_17 ?v_10 ?v_7) (or ?v_10 ?v_9 ?v_4 ?v_1 ?v_13 ?v_7 ?v_14 ?v_3 ?v_5 ?v_17) (or ?v_10 ?v_9 ?v_4 ?v_9 ?v_18 ?v_17 ?v_14 ?v_14 ?v_5 ?v_17) (or ?v_10 ?v_9 ?v_18 ?v_1 ?v_13 ?v_7 ?v_17 ?v_7 ?v_10 ?v_17) (or ?v_10 ?v_9 ?v_18 ?v_9 ?v_18 ?v_17 ?v_17 ?v_17 ?v_10 ?v_17) (or ?v_2 ?v_1 ?v_84 ?v_1) (or ?v_4 ?v_9 (p1 c_1 ?v_25) ?v_1) (or ?v_13 ?v_1 (p1 c_0 ?v_26) ?v_9) (or ?v_18 ?v_9 ?v_85 ?v_9) (or ?v_2 ?v_1 (p4 ?v_64) ?v_2 ?v_1 ?v_8 ?v_1 ?v_2) (or ?v_2 ?v_1 (p4 ?v_68) ?v_4 ?v_9 ?v_20 ?v_1 ?v_13) (or ?v_4 ?v_9 (p4 ?v_66) ?v_2 ?v_1 ?v_11 ?v_1 ?v_4) (or ?v_4 ?v_9 (p4 ?v_70) ?v_4 ?v_9 ?v_21 ?v_1 ?v_18) (or ?v_13 ?v_1 (p4 ?v_65) ?v_13 ?v_1 ?v_16 ?v_9 ?v_2) (or ?v_13 ?v_1 (p4 ?v_69) ?v_18 ?v_9 ?v_22 ?v_9 ?v_13) (or ?v_18 ?v_9 (p4 ?v_67) ?v_13 ?v_1 ?v_19 ?v_9 ?v_4) (or ?v_18 ?v_9 (p4 ?v_71) ?v_18 ?v_9 ?v_23 ?v_9 ?v_18) (or ?v_2 ?v_2 ?v_2 ?v_28 ?v_1 ?v_3 ?v_3 ?v_1 ?v_5 ?v_1 ?v_3) (or ?v_2 ?v_2 ?v_2 ?v_28 ?v_1 ?v_7 ?v_7 ?v_1 ?v_10 ?v_1 ?v_7) (or ?v_2 ?v_13 ?v_4 ?v_29 ?v_1 ?v_14 ?v_3 ?v_1 ?v_5 ?v_9 ?v_3) (or ?v_2 ?v_13 ?v_4 ?v_29 ?v_1 ?v_17 ?v_7 ?v_1 ?v_10 ?v_9 ?v_7) (or ?v_4 ?v_4 ?v_2 ?v_30 ?v_1 ?v_3 ?v_3 ?v_9 ?v_5 ?v_1 ?v_14) (or ?v_4 ?v_4 ?v_2 ?v_30 ?v_1 ?v_7 ?v_7 ?v_9 ?v_10 ?v_1 ?v_17) (or ?v_4 ?v_18 ?v_4 ?v_31 ?v_1 ?v_14 ?v_3 ?v_9 ?v_5 ?v_9 ?v_14) (or ?v_4 ?v_18 ?v_4 ?v_31 ?v_1 ?v_17 ?v_7 ?v_9 ?v_10 ?v_9 ?v_17) (or ?v_13 ?v_2 ?v_13 ?v_32 ?v_9 ?v_3 ?v_14 ?v_1 ?v_5 ?v_1 ?v_3) (or ?v_13 ?v_2 ?v_13 ?v_32 ?v_9 ?v_7 ?v_17 ?v_1 ?v_10 ?v_1 ?v_7) (or ?v_13 ?v_13 ?v_18 ?v_33 ?v_9 ?v_14 ?v_14 ?v_1 ?v_5 ?v_9 ?v_3) (or ?v_13 ?v_13 ?v_18 ?v_33 ?v_9 ?v_17 ?v_17 ?v_1 ?v_10 ?v_9 ?v_7) (or ?v_18 ?v_4 ?v_13 ?v_34 ?v_9 ?v_3 ?v_14 ?v_9 ?v_5 ?v_1 ?v_14) (or ?v_18 ?v_4 ?v_13 ?v_34 ?v_9 ?v_7 ?v_17 ?v_9 ?v_10 ?v_1 ?v_17) (or ?v_18 ?v_18 ?v_18 ?v_35 ?v_9 ?v_14 ?v_14 ?v_9 ?v_5 ?v_9 ?v_14) (or ?v_18 ?v_18 ?v_18 ?v_35 ?v_9 ?v_17 ?v_17 ?v_9 ?v_10 ?v_9 ?v_17) (or ?v_36 ?v_37 ?v_1 (p3 ?v_52) ?v_2 ?v_36 ?v_37) (or ?v_36 ?v_40 ?v_1 (p3 ?v_54) ?v_4 ?v_38 ?v_37) (or ?v_36 ?v_39 ?v_9 (p3 ?v_56) ?v_2 ?v_36 ?v_39) (or ?v_36 ?v_41 ?v_9 (p3 ?v_58) ?v_4 ?v_38 ?v_39) (or ?v_38 ?v_37 ?v_1 (p3 ?v_53) ?v_13 ?v_36 ?v_40) (or ?v_38 ?v_40 ?v_1 (p3 ?v_55) ?v_18 ?v_38 ?v_40) (or ?v_38 ?v_39 ?v_9 (p3 ?v_57) ?v_13 ?v_36 ?v_41) (or ?v_38 ?v_41 ?v_9 (p3 ?v_59) ?v_18 ?v_38 ?v_41) (or ?v_5 (not (p1 ?v_94 c_0))) (or ?v_10 (not (p1 ?v_95 c_1))) (or ?v_1 ?v_2 ?v_42 ?v_1 ?v_28 ?v_2 ?v_1 ?v_2) (or ?v_1 ?v_2 (p10 c_1 ?v_43) ?v_9 ?v_32 ?v_13 ?v_1 ?v_13) (or ?v_1 ?v_13 ?v_46 ?v_1 ?v_29 ?v_4 ?v_9 ?v_2) (or ?v_1 ?v_13 ?v_93 ?v_9 ?v_33 ?v_18 ?v_9 ?v_13) (or ?v_9 ?v_4 ?v_90 ?v_1 ?v_30 ?v_2 ?v_1 ?v_4) (or ?v_9 ?v_4 ?v_45 ?v_9 ?v_34 ?v_13 ?v_1 ?v_18) (or ?v_9 ?v_18 (p10 c_0 ?v_48) ?v_1 ?v_31 ?v_4 ?v_9 ?v_4) (or ?v_9 ?v_18 ?v_49 ?v_9 ?v_35 ?v_18 ?v_9 ?v_18) (p9 c18) (or ?v_2 ?v_1 ?v_2 ?v_2 ?v_28 ?v_1 ?v_42 ?v_1) (or ?v_2 ?v_9 ?v_13 ?v_13 ?v_32 ?v_1 ?v_92 ?v_1) (or ?v_4 ?v_1 ?v_2 ?v_4 ?v_30 ?v_1 (p10 c_1 ?v_44) ?v_9) (or ?v_4 ?v_9 ?v_13 ?v_18 ?v_34 ?v_1 ?v_45 ?v_9) (or ?v_13 ?v_1 ?v_4 ?v_2 ?v_29 ?v_9 ?v_46 ?v_1) (or ?v_13 ?v_9 ?v_18 ?v_13 ?v_33 ?v_9 (p10 c_0 ?v_47) ?v_1) (or ?v_18 ?v_1 ?v_4 ?v_4 ?v_31 ?v_9 ?v_91 ?v_9) (or ?v_18 ?v_9 ?v_18 ?v_18 ?v_35 ?v_9 ?v_49 ?v_9) (or ?v_1 ?v_2 ?v_1 ?v_50 ?v_28 ?v_1 ?v_50 ?v_50 ?v_2 ?v_2) (or ?v_1 ?v_2 ?v_9 ?v_51 ?v_30 ?v_1 ?v_50 ?v_50 ?v_4 ?v_4) (or ?v_1 ?v_13 ?v_1 ?v_50 ?v_32 ?v_9 ?v_50 ?v_51 ?v_13 ?v_2) (or ?v_1 ?v_13 ?v_9 ?v_51 ?v_34 ?v_9 ?v_50 ?v_51 ?v_18 ?v_4) (or ?v_9 ?v_4 ?v_1 ?v_50 ?v_29 ?v_1 ?v_51 ?v_50 ?v_2 ?v_13) (or ?v_9 ?v_4 ?v_9 ?v_51 ?v_31 ?v_1 ?v_51 ?v_50 ?v_4 ?v_18) (or ?v_9 ?v_18 ?v_1 ?v_50 ?v_33 ?v_9 ?v_51 ?v_51 ?v_13 ?v_13) (or ?v_9 ?v_18 ?v_9 ?v_51 ?v_35 ?v_9 ?v_51 ?v_51 ?v_18 ?v_18) (or ?v_36 (p10 ?v_100 c_0)) (or ?v_38 (p10 ?v_101 c_1)) (or ?v_5 (p1 ?v_60 c_0)) (or ?v_10 (p1 ?v_62 c_1)) (or ?v_37 ?v_1 ?v_80 ?v_2 ?v_37 ?v_36 ?v_36) (or ?v_37 ?v_1 (p10 ?v_53 c_1) ?v_13 ?v_40 ?v_38 ?v_36) (or ?v_40 ?v_1 (p10 ?v_54 c_0) ?v_4 ?v_37 ?v_36 ?v_38) (or ?v_40 ?v_1 ?v_81 ?v_18 ?v_40 ?v_38 ?v_38) (or ?v_39 ?v_9 ?v_82 ?v_2 ?v_39 ?v_36 ?v_36) (or ?v_39 ?v_9 (p10 ?v_57 c_1) ?v_13 ?v_41 ?v_38 ?v_36) (or ?v_41 ?v_9 (p10 ?v_58 c_0) ?v_4 ?v_39 ?v_36 ?v_38) (or ?v_41 ?v_9 ?v_83 ?v_18 ?v_41 ?v_38 ?v_38) (or ?v_5 (not (= ?v_60 ?v_61))) (or ?v_10 (not (= ?v_62 ?v_63))) (or ?v_5 (p3 ?v_60)) (or ?v_10 (p3 ?v_62)) (or ?v_2 ?v_1 ?v_76 ?v_1 ?v_8 ?v_2 ?v_1 ?v_2) (or ?v_2 ?v_1 ?v_77 ?v_1 ?v_16 ?v_13 ?v_9 ?v_13) (or ?v_4 ?v_1 ?v_86 ?v_9 ?v_11 ?v_2 ?v_1 ?v_4) (or ?v_4 ?v_1 (p1 c_0 ?v_67) ?v_9 ?v_19 ?v_13 ?v_9 ?v_18) (or ?v_13 ?v_9 (p1 c_1 ?v_68) ?v_1 ?v_20 ?v_4 ?v_1 ?v_2) (or ?v_13 ?v_9 ?v_89 ?v_1 ?v_22 ?v_18 ?v_9 ?v_13) (or ?v_18 ?v_9 ?v_78 ?v_9 ?v_21 ?v_4 ?v_1 ?v_4) (or ?v_18 ?v_9 ?v_79 ?v_9 ?v_23 ?v_18 ?v_9 ?v_18) (or ?v_1 ?v_1 ?v_2 ?v_2 (p9 ?v_72) ?v_2 ?v_1 ?v_28) (or ?v_1 ?v_1 ?v_13 ?v_2 (p9 ?v_73) ?v_4 ?v_9 ?v_29) (or ?v_1 ?v_9 ?v_4 ?v_4 (p9 ?v_44) ?v_2 ?v_1 ?v_30) (or ?v_1 ?v_9 ?v_18 ?v_4 (p9 ?v_48) ?v_4 ?v_9 ?v_31) (or ?v_9 ?v_1 ?v_2 ?v_13 (p9 ?v_43) ?v_13 ?v_1 ?v_32) (or ?v_9 ?v_1 ?v_13 ?v_13 (p9 ?v_47) ?v_18 ?v_9 ?v_33) (or ?v_9 ?v_9 ?v_4 ?v_18 (p9 ?v_74) ?v_13 ?v_1 ?v_34) (or ?v_9 ?v_9 ?v_18 ?v_18 (p9 ?v_75) ?v_18 ?v_9 ?v_35) (or ?v_76 ?v_8 ?v_1 ?v_2 ?v_1 ?v_1 ?v_2 ?v_2) (or ?v_88 ?v_20 ?v_1 ?v_4 ?v_9 ?v_1 ?v_13 ?v_2) (or ?v_77 ?v_16 ?v_9 ?v_13 ?v_1 ?v_1 ?v_2 ?v_13) (or (p1 c_0 ?v_69) ?v_22 ?v_9 ?v_18 ?v_9 ?v_1 ?v_13 ?v_13) (or (p1 c_1 ?v_66) ?v_11 ?v_1 ?v_2 ?v_1 ?v_9 ?v_4 ?v_4) (or ?v_78 ?v_21 ?v_1 ?v_4 ?v_9 ?v_9 ?v_18 ?v_4) (or ?v_87 ?v_19 ?v_9 ?v_13 ?v_1 ?v_9 ?v_4 ?v_18) (or ?v_79 ?v_23 ?v_9 ?v_18 ?v_9 ?v_9 ?v_18 ?v_18) (or ?v_37 ?v_2 ?v_36 ?v_36 ?v_80 ?v_37 ?v_1) (or ?v_37 ?v_13 ?v_36 ?v_38 (p10 ?v_53 c_0) ?v_40 ?v_1) (or ?v_40 ?v_4 ?v_38 ?v_36 (p10 ?v_54 c_1) ?v_37 ?v_1) (or ?v_40 ?v_18 ?v_38 ?v_38 ?v_81 ?v_40 ?v_1) (or ?v_39 ?v_2 ?v_36 ?v_36 ?v_82 ?v_39 ?v_9) (or ?v_39 ?v_13 ?v_36 ?v_38 (p10 ?v_57 c_0) ?v_41 ?v_9) (or ?v_41 ?v_4 ?v_38 ?v_36 (p10 ?v_58 c_1) ?v_39 ?v_9) (or ?v_41 ?v_18 ?v_38 ?v_38 ?v_83 ?v_41 ?v_9) (p4 c8) (or ?v_1 ?v_2 ?v_84 ?v_1) (or ?v_1 ?v_13 (p1 c_1 ?v_26) ?v_9) (or ?v_9 ?v_4 (p1 c_0 ?v_25) ?v_1) (or ?v_9 ?v_18 ?v_85 ?v_9) (or ?v_2 ?v_2 ?v_1 ?v_76 ?v_8 ?v_2 ?v_1 ?v_1) (or ?v_2 ?v_13 ?v_1 (p1 c_1 ?v_65) ?v_16 ?v_13 ?v_1 ?v_9) (or ?v_4 ?v_4 ?v_1 ?v_86 ?v_11 ?v_2 ?v_9 ?v_1) (or ?v_4 ?v_18 ?v_1 ?v_87 ?v_19 ?v_13 ?v_9 ?v_9) (or ?v_13 ?v_2 ?v_9 ?v_88 ?v_20 ?v_4 ?v_1 ?v_1) (or ?v_13 ?v_13 ?v_9 ?v_89 ?v_22 ?v_18 ?v_1 ?v_9) (or ?v_18 ?v_4 ?v_9 (p1 c_0 ?v_70) ?v_21 ?v_4 ?v_9 ?v_1) (or ?v_18 ?v_18 ?v_9 ?v_79 ?v_23 ?v_18 ?v_9 ?v_9) (or ?v_28 ?v_1 ?v_37 ?v_37 ?v_36 ?v_37 ?v_37 ?v_2 ?v_1 ?v_36 ?v_37 ?v_2 ?v_1 ?v_2 ?v_2 ?v_37) (or ?v_28 ?v_1 ?v_37 ?v_40 ?v_36 ?v_37 ?v_40 ?v_4 ?v_1 ?v_38 ?v_40 ?v_2 ?v_1 ?v_2 ?v_2 ?v_37) (or ?v_28 ?v_1 ?v_40 ?v_37 ?v_38 ?v_40 ?v_37 ?v_13 ?v_1 ?v_36 ?v_37 ?v_2 ?v_1 ?v_2 ?v_2 ?v_40) (or ?v_28 ?v_1 ?v_40 ?v_40 ?v_38 ?v_40 ?v_40 ?v_18 ?v_1 ?v_38 ?v_40 ?v_2 ?v_1 ?v_2 ?v_2 ?v_40) (or ?v_30 ?v_1 ?v_39 ?v_37 ?v_36 ?v_37 ?v_39 ?v_2 ?v_9 ?v_36 ?v_37 ?v_4 ?v_1 ?v_4 ?v_2 ?v_37) (or ?v_30 ?v_1 ?v_39 ?v_40 ?v_36 ?v_37 ?v_41 ?v_4 ?v_9 ?v_38 ?v_40 ?v_4 ?v_1 ?v_4 ?v_2 ?v_37) (or ?v_30 ?v_1 ?v_41 ?v_37 ?v_38 ?v_40 ?v_39 ?v_13 ?v_9 ?v_36 ?v_37 ?v_4 ?v_1 ?v_4 ?v_2 ?v_40) (or ?v_30 ?v_1 ?v_41 ?v_40 ?v_38 ?v_40 ?v_41 ?v_18 ?v_9 ?v_38 ?v_40 ?v_4 ?v_1 ?v_4 ?v_2 ?v_40) (or ?v_29 ?v_9 ?v_37 ?v_37 ?v_36 ?v_37 ?v_37 ?v_2 ?v_1 ?v_36 ?v_39 ?v_13 ?v_1 ?v_2 ?v_4 ?v_39) (or ?v_29 ?v_9 ?v_37 ?v_40 ?v_36 ?v_37 ?v_40 ?v_4 ?v_1 ?v_38 ?v_41 ?v_13 ?v_1 ?v_2 ?v_4 ?v_39) (or ?v_29 ?v_9 ?v_40 ?v_37 ?v_38 ?v_40 ?v_37 ?v_13 ?v_1 ?v_36 ?v_39 ?v_13 ?v_1 ?v_2 ?v_4 ?v_41) (or ?v_29 ?v_9 ?v_40 ?v_40 ?v_38 ?v_40 ?v_40 ?v_18 ?v_1 ?v_38 ?v_41 ?v_13 ?v_1 ?v_2 ?v_4 ?v_41) (or ?v_31 ?v_9 ?v_39 ?v_37 ?v_36 ?v_37 ?v_39 ?v_2 ?v_9 ?v_36 ?v_39 ?v_18 ?v_1 ?v_4 ?v_4 ?v_39) (or ?v_31 ?v_9 ?v_39 ?v_40 ?v_36 ?v_37 ?v_41 ?v_4 ?v_9 ?v_38 ?v_41 ?v_18 ?v_1 ?v_4 ?v_4 ?v_39) (or ?v_31 ?v_9 ?v_41 ?v_37 ?v_38 ?v_40 ?v_39 ?v_13 ?v_9 ?v_36 ?v_39 ?v_18 ?v_1 ?v_4 ?v_4 ?v_41) (or ?v_31 ?v_9 ?v_41 ?v_40 ?v_38 ?v_40 ?v_41 ?v_18 ?v_9 ?v_38 ?v_41 ?v_18 ?v_1 ?v_4 ?v_4 ?v_41) (or ?v_32 ?v_1 ?v_37 ?v_39 ?v_36 ?v_39 ?v_37 ?v_2 ?v_1 ?v_36 ?v_37 ?v_2 ?v_9 ?v_13 ?v_13 ?v_37) (or ?v_32 ?v_1 ?v_37 ?v_41 ?v_36 ?v_39 ?v_40 ?v_4 ?v_1 ?v_38 ?v_40 ?v_2 ?v_9 ?v_13 ?v_13 ?v_37) (or ?v_32 ?v_1 ?v_40 ?v_39 ?v_38 ?v_41 ?v_37 ?v_13 ?v_1 ?v_36 ?v_37 ?v_2 ?v_9 ?v_13 ?v_13 ?v_40) (or ?v_32 ?v_1 ?v_40 ?v_41 ?v_38 ?v_41 ?v_40 ?v_18 ?v_1 ?v_38 ?v_40 ?v_2 ?v_9 ?v_13 ?v_13 ?v_40) (or ?v_34 ?v_1 ?v_39 ?v_39 ?v_36 ?v_39 ?v_39 ?v_2 ?v_9 ?v_36 ?v_37 ?v_4 ?v_9 ?v_18 ?v_13 ?v_37) (or ?v_34 ?v_1 ?v_39 ?v_41 ?v_36 ?v_39 ?v_41 ?v_4 ?v_9 ?v_38 ?v_40 ?v_4 ?v_9 ?v_18 ?v_13 ?v_37) (or ?v_34 ?v_1 ?v_41 ?v_39 ?v_38 ?v_41 ?v_39 ?v_13 ?v_9 ?v_36 ?v_37 ?v_4 ?v_9 ?v_18 ?v_13 ?v_40) (or ?v_34 ?v_1 ?v_41 ?v_41 ?v_38 ?v_41 ?v_41 ?v_18 ?v_9 ?v_38 ?v_40 ?v_4 ?v_9 ?v_18 ?v_13 ?v_40) (or ?v_33 ?v_9 ?v_37 ?v_39 ?v_36 ?v_39 ?v_37 ?v_2 ?v_1 ?v_36 ?v_39 ?v_13 ?v_9 ?v_13 ?v_18 ?v_39) (or ?v_33 ?v_9 ?v_37 ?v_41 ?v_36 ?v_39 ?v_40 ?v_4 ?v_1 ?v_38 ?v_41 ?v_13 ?v_9 ?v_13 ?v_18 ?v_39) (or ?v_33 ?v_9 ?v_40 ?v_39 ?v_38 ?v_41 ?v_37 ?v_13 ?v_1 ?v_36 ?v_39 ?v_13 ?v_9 ?v_13 ?v_18 ?v_41) (or ?v_33 ?v_9 ?v_40 ?v_41 ?v_38 ?v_41 ?v_40 ?v_18 ?v_1 ?v_38 ?v_41 ?v_13 ?v_9 ?v_13 ?v_18 ?v_41) (or ?v_35 ?v_9 ?v_39 ?v_39 ?v_36 ?v_39 ?v_39 ?v_2 ?v_9 ?v_36 ?v_39 ?v_18 ?v_9 ?v_18 ?v_18 ?v_39) (or ?v_35 ?v_9 ?v_39 ?v_41 ?v_36 ?v_39 ?v_41 ?v_4 ?v_9 ?v_38 ?v_41 ?v_18 ?v_9 ?v_18 ?v_18 ?v_39) (or ?v_35 ?v_9 ?v_41 ?v_39 ?v_38 ?v_41 ?v_39 ?v_13 ?v_9 ?v_36 ?v_39 ?v_18 ?v_9 ?v_18 ?v_18 ?v_41) (or ?v_35 ?v_9 ?v_41 ?v_41 ?v_38 ?v_41 ?v_41 ?v_18 ?v_9 ?v_38 ?v_41 ?v_18 ?v_9 ?v_18 ?v_18 ?v_41) (or ?v_2 ?v_1 ?v_2 ?v_28 ?v_1 ?v_1 ?v_2 ?v_42) (or ?v_2 ?v_1 ?v_4 ?v_30 ?v_1 ?v_9 ?v_4 ?v_90) (or ?v_4 ?v_1 ?v_13 ?v_29 ?v_9 ?v_1 ?v_2 (p10 c_1 ?v_73)) (or ?v_4 ?v_1 ?v_18 ?v_31 ?v_9 ?v_9 ?v_4 ?v_91) (or ?v_13 ?v_9 ?v_2 ?v_32 ?v_1 ?v_1 ?v_13 ?v_92) (or ?v_13 ?v_9 ?v_4 ?v_34 ?v_1 ?v_9 ?v_18 (p10 c_0 ?v_74)) (or ?v_18 ?v_9 ?v_13 ?v_33 ?v_9 ?v_1 ?v_13 ?v_93) (or ?v_18 ?v_9 ?v_18 ?v_35 ?v_9 ?v_9 ?v_18 ?v_49) (or (p3 ?v_94) ?v_5) (or (p3 ?v_95) ?v_10) (or (not (= c_0 ?v_52)) ?v_37 ?v_37 ?v_36 ?v_1 ?v_2 ?v_36) (or (not (= c_0 ?v_54)) ?v_37 ?v_40 ?v_36 ?v_1 ?v_4 ?v_38) (or (not (= c_0 ?v_53)) ?v_40 ?v_37 ?v_38 ?v_1 ?v_13 ?v_36) (or (not (= c_0 ?v_55)) ?v_40 ?v_40 ?v_38 ?v_1 ?v_18 ?v_38) (or (not (= c_1 ?v_56)) ?v_39 ?v_39 ?v_36 ?v_9 ?v_2 ?v_36) (or (not (= c_1 ?v_58)) ?v_39 ?v_41 ?v_36 ?v_9 ?v_4 ?v_38) (or (not (= c_1 ?v_57)) ?v_41 ?v_39 ?v_38 ?v_9 ?v_13 ?v_36) (or (not (= c_1 ?v_59)) ?v_41 ?v_41 ?v_38 ?v_9 ?v_18 ?v_38) (or (p3 ?v_61) ?v_5) (or (p3 ?v_63) ?v_10) (or ?v_36 ?v_3 ?v_2 ?v_37 ?v_96 ?v_37 ?v_1 ?v_5 ?v_3 ?v_1) (or ?v_36 ?v_3 ?v_13 ?v_37 ?v_96 ?v_39 ?v_1 ?v_5 ?v_14 ?v_9) (or ?v_36 ?v_7 ?v_2 ?v_37 ?v_97 ?v_37 ?v_1 ?v_10 ?v_7 ?v_1) (or ?v_36 ?v_7 ?v_13 ?v_37 ?v_97 ?v_39 ?v_1 ?v_10 ?v_17 ?v_9) (or ?v_36 ?v_14 ?v_4 ?v_39 ?v_96 ?v_37 ?v_9 ?v_5 ?v_3 ?v_1) (or ?v_36 ?v_14 ?v_18 ?v_39 ?v_96 ?v_39 ?v_9 ?v_5 ?v_14 ?v_9) (or ?v_36 ?v_17 ?v_4 ?v_39 ?v_97 ?v_37 ?v_9 ?v_10 ?v_7 ?v_1) (or ?v_36 ?v_17 ?v_18 ?v_39 ?v_97 ?v_39 ?v_9 ?v_10 ?v_17 ?v_9) (or ?v_38 ?v_3 ?v_2 ?v_40 ?v_98 ?v_40 ?v_1 ?v_5 ?v_3 ?v_1) (or ?v_38 ?v_3 ?v_13 ?v_40 ?v_98 ?v_41 ?v_1 ?v_5 ?v_14 ?v_9) (or ?v_38 ?v_7 ?v_2 ?v_40 ?v_99 ?v_40 ?v_1 ?v_10 ?v_7 ?v_1) (or ?v_38 ?v_7 ?v_13 ?v_40 ?v_99 ?v_41 ?v_1 ?v_10 ?v_17 ?v_9) (or ?v_38 ?v_14 ?v_4 ?v_41 ?v_98 ?v_40 ?v_9 ?v_5 ?v_3 ?v_1) (or ?v_38 ?v_14 ?v_18 ?v_41 ?v_98 ?v_41 ?v_9 ?v_5 ?v_14 ?v_9) (or ?v_38 ?v_17 ?v_4 ?v_41 ?v_99 ?v_40 ?v_9 ?v_10 ?v_7 ?v_1) (or ?v_38 ?v_17 ?v_18 ?v_41 ?v_99 ?v_41 ?v_9 ?v_10 ?v_17 ?v_9) (or ?v_36 (p3 ?v_100)) (or ?v_38 (p3 ?v_101)) (or ?v_36 (not (p10 ?v_102 c_0))) (or ?v_38 (not (p10 ?v_103 c_1))) (or (= ?v_64 c_0) (= ?v_64 c_1)) (or (= ?v_66 c_0) (= ?v_66 c_1)) (or (= ?v_68 c_0) (= ?v_68 c_1)) (or (= ?v_70 c_0) (= ?v_70 c_1)) (or (= ?v_65 c_0) (= ?v_65 c_1)) (or (= ?v_67 c_0) (= ?v_67 c_1)) (or (= ?v_69 c_0) (= ?v_69 c_1)) (or (= ?v_71 c_0) (= ?v_71 c_1)) (or (= ?v_52 c_0) (= ?v_52 c_1)) (or (= ?v_56 c_0) (= ?v_56 c_1)) (or (= ?v_54 c_0) (= ?v_54 c_1)) (or (= ?v_58 c_0) (= ?v_58 c_1)) (or (= ?v_53 c_0) (= ?v_53 c_1)) (or (= ?v_57 c_0) (= ?v_57 c_1)) (or (= ?v_55 c_0) (= ?v_55 c_1)) (or (= ?v_59 c_0) (= ?v_59 c_1)) (or (= ?v_72 c_0) (= ?v_72 c_1)) (or (= ?v_44 c_0) (= ?v_44 c_1)) (or (= ?v_73 c_0) (= ?v_73 c_1)) (or (= ?v_48 c_0) (= ?v_48 c_1)) (or (= ?v_43 c_0) (= ?v_43 c_1)) (or (= ?v_74 c_0) (= ?v_74 c_1)) (or (= ?v_47 c_0) (= ?v_47 c_1)) (or (= ?v_75 c_0) (= ?v_75 c_1)) (or (= ?v_24 c_0) (= ?v_24 c_1)) (or (= ?v_25 c_0) (= ?v_25 c_1)) (or (= ?v_26 c_0) (= ?v_26 c_1)) (or (= ?v_27 c_0) (= ?v_27 c_1)) (or (= ?v_102 c_0) (= ?v_102 c_1)) (or (= ?v_103 c_0) (= ?v_103 c_1)) (or (= ?v_61 c_0) (= ?v_61 c_1)) (or (= ?v_63 c_0) (= ?v_63 c_1)) (or (= ?v_94 c_0) (= ?v_94 c_1)) (or (= ?v_95 c_0) (= ?v_95 c_1)) (or (= ?v_100 c_0) (= ?v_100 c_1)) (or (= ?v_101 c_0) (= ?v_101 c_1)) (or (= ?v_60 c_0) (= ?v_60 c_1)) (or (= ?v_62 c_0) (= ?v_62 c_1)) (or (= c18 c_0) (= c18 c_1)) (or (= c8 c_0) (= c8 c_1))))))))))))))))))))))
(check-sat)
(exit)
