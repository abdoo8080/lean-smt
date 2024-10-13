(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
Generated by: David Deharbe, CLEARSY
Generated on: 2019-09-09
Generator: bxml;pog;pog2smt (Atelier B)
Application: Event-B
Target solver: CVC4, Z3
|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)
; Prelude
(declare-sort U 0)
(declare-fun |*i| (U U) U)
(declare-fun |+i| (U U) U)
(declare-fun |-i| (U U) U)
(declare-fun idiv (U U) U)
(declare-fun |*r| (U U) U)
(declare-fun |+r| (U U) U)
(declare-fun |-r| (U U) U)
(declare-fun rdiv (U U) U)
(declare-fun modulo (U U) U)
(declare-fun |<i| (U U) Bool)
(declare-fun |<=i| (U U) Bool)
(declare-fun |>i| (U U) Bool)
(declare-fun |>=i| (U U) Bool)
(declare-fun |<r| (U U) Bool)
(declare-fun |<=r| (U U) Bool)
(declare-fun |>r| (U U) Bool)
(declare-fun |>=r| (U U) Bool)
(declare-fun iuminus (U) U)
(declare-fun ruminus (U) U)
(declare-fun TRUE () U)
(declare-fun FALSE () U)
(assert (not (= TRUE FALSE)))
(declare-fun empty () U)
(declare-fun bool (Bool) U)
(declare-fun BOOL () U)
(declare-fun INT () U)
(declare-fun INTEGER () U)
(declare-fun NAT () U)
(declare-fun NAT1 () U)
(declare-fun NATURAL () U)
(declare-fun NATURAL1 () U)
(declare-fun FLOAT () U)
(declare-fun MaxInt () U)
(declare-fun MinInt () U)
(declare-fun |STRING| () U)
(declare-fun REAL () U)
(declare-fun set_prod (U U) U)
(declare-fun set_diff (U U) U)
(declare-fun mapplet (U U) U)
(declare-fun |**i| (U U) U)
(declare-fun |**r| (U U) U)
(declare-fun |+->| (U U) U)
(declare-fun |+->>| (U U) U)
(declare-fun |-->| (U U) U)
(declare-fun |-->>| (U U) U)
(declare-fun |<->| (U U) U)
(declare-fun |>+>| (U U) U)
(declare-fun |>->| (U U) U)
(declare-fun |>+>>| (U U) U)
(declare-fun |>->>| (U U) U)
(declare-fun |->| (U U) U)
(declare-fun interval (U U) U)
(declare-fun composition (U U) U)
(declare-fun binary_inter (U U) U)
(declare-fun restriction_head (U U) U)
(declare-fun semicolon (U U) U)
(declare-fun |<+| (U U) U)
(declare-fun |<-| (U U) U)
(declare-fun domain_subtraction (U U) U)
(declare-fun domain_restriction (U U) U)
(declare-fun |><| (U U) U)
(declare-fun parallel_product (U U) U)
(declare-fun binary_union (U U) U)
(declare-fun restriction_tail (U U) U)
(declare-fun concatenate (U U) U)
(declare-fun range_restriction (U U) U)
(declare-fun range_subtraction (U U) U)
(declare-fun image (U U) U)
(declare-fun apply (U U) U)
(declare-fun prj1 (U U) U)
(declare-fun prj2 (U U) U)
(declare-fun iterate (U U) U)
(declare-fun |const| (U U) U)
(declare-fun rank (U U) U)
(declare-fun father (U U) U)
(declare-fun subtree (U U) U)
(declare-fun arity (U U) U)
(declare-fun |+f| (U U) U)
(declare-fun |-f| (U U) U)
(declare-fun |*f| (U U) U)
(declare-fun |fdiv| (U U) U)
(declare-fun tbin (U U U) U)
(declare-fun son (U U U) U)
(declare-fun mem (U U) Bool)
(declare-fun subset (U U) Bool)
(declare-fun strict_subset (U U) Bool)
(declare-fun |<=f| (U U) Bool)
(declare-fun |<f| (U U) Bool)
(declare-fun |>=f| (U U) Bool)
(declare-fun |>f| (U U) Bool)
(declare-fun imax (U) U)
(declare-fun imin (U) U)
(declare-fun rmax (U) U)
(declare-fun rmin (U) U)
(declare-fun card (U) U)
(declare-fun dom (U) U)
(declare-fun ran (U) U)
(declare-fun POW (U) U)
(declare-fun POW1 (U) U)
(declare-fun FIN (U) U)
(declare-fun FIN1 (U) U)
(declare-fun union (U) U)
(declare-fun inter (U) U)
(declare-fun seq (U) U)
(declare-fun seq1 (U) U)
(declare-fun iseq (U) U)
(declare-fun iseq1 (U) U)
(declare-fun inverse (U) U)
(declare-fun size (U) U)
(declare-fun perm (U) U)
(declare-fun first (U) U)
(declare-fun last (U) U)
(declare-fun id (U) U)
(declare-fun closure (U) U)
(declare-fun closure1 (U) U)
(declare-fun tail (U) U)
(declare-fun front (U) U)
(declare-fun reverse (U) U)
(declare-fun rev (U) U)
(declare-fun conc (U) U)
(declare-fun succ (U) U)
(declare-fun pred (U) U)
(declare-fun rel (U) U)
(declare-fun fnc (U) U)
(declare-fun real (U) U)
(declare-fun floor (U) U)
(declare-fun ceiling (U) U)
(declare-fun tree (U) U)
(declare-fun btree (U) U)
(declare-fun top (U) U)
(declare-fun sons (U) U)
(declare-fun prefix (U) U)
(declare-fun postfix (U) U)
(declare-fun sizet (U) U)
(declare-fun mirror (U) U)
(declare-fun left (U) U)
(declare-fun right (U) U)
(declare-fun infix (U) U)
(declare-fun ubin (U) U)
(declare-fun SEQ (U) U)
(declare-fun SET (U) U)
; Opaque formulas
(declare-fun e0 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_11 () U)
(declare-fun g_s11_12 () U)
(declare-fun g_s12_13 () U)
(declare-fun g_s13_14 () U)
(declare-fun g_s14_15 () U)
(declare-fun g_s15_16 () U)
(declare-fun g_s16_17 () U)
(declare-fun g_s17_18 () U)
(declare-fun g_s18_19 () U)
(declare-fun g_s19_20 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_21 () U)
(declare-fun g_s21_22 () U)
(declare-fun g_s22_23 () U)
(declare-fun g_s23_24 () U)
(declare-fun g_s24_25 () U)
(declare-fun g_s25_26 () U)
(declare-fun g_s26_27 () U)
(declare-fun g_s27_28 () U)
(declare-fun g_s28_29 () U)
(declare-fun g_s29_31 () U)
(declare-fun g_s3_4 () U)
(declare-fun g_s30_30 () U)
(declare-fun g_s31_32 () U)
(declare-fun g_s32_33 () U)
(declare-fun g_s33_34 () U)
(declare-fun g_s34_35 () U)
(declare-fun g_s35_36 () U)
(declare-fun g_s36_37 () U)
(declare-fun g_s37_38 () U)
(declare-fun g_s38_39 () U)
(declare-fun g_s39_40 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s40_41 () U)
(declare-fun g_s41_42 () U)
(declare-fun g_s42_43 () U)
(declare-fun g_s43_44 () U)
(declare-fun g_s44_45 () U)
(declare-fun g_s45_46 () U)
(declare-fun g_s46_47 () U)
(declare-fun g_s47_49 () U)
(declare-fun g_s48_48 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_50 () U)
(declare-fun g_s50$1_51 () U)
(declare-fun g_s51_52 () U)
(declare-fun g_s51$1_53 () U)
(declare-fun g_s52_54 () U)
(declare-fun g_s52$1_55 () U)
(declare-fun g_s53_56 () U)
(declare-fun g_s53$1_57 () U)
(declare-fun g_s54_58 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s9_10 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (= g_s0_1 (SET (mapplet g_s5_6 (mapplet g_s4_5 (mapplet g_s3_4 (mapplet g_s2_3 g_s1_2)))))) (= g_s6_7 (SET (mapplet g_s9_10 (mapplet g_s8_9 g_s7_8)))) (not (= g_s10_11 empty)) (not (= g_s11_12 empty)) (= g_s12_13 INT) (= g_s13_14 NAT) (= g_s14_15 NAT1) (subset g_s14_15 g_s13_14) (subset g_s13_14 g_s12_13) (= g_s15_16 INT) (= g_s16_17 NAT) (subset g_s16_17 g_s15_16) (mem g_s17_18 g_s12_13) (mem g_s17_18 g_s13_14) (not (mem g_s17_18 g_s14_15)) (mem g_s18_19 g_s12_13) (not (mem g_s18_19 g_s13_14)) (mem g_s19_20 g_s15_16) (mem g_s19_20 g_s16_17) (mem g_s20_21 g_s15_16) (not (mem g_s20_21 g_s16_17)) (= g_s21_22 INT) (= g_s22_23 INT) (= g_s23_24 NATURAL) (= g_s24_25 NATURAL) (subset g_s25_26 g_s10_11) (mem g_s26_27 g_s10_11) (mem g_s26_27 g_s25_26) (mem g_s27_28 g_s10_11) (not (mem g_s27_28 g_s25_26)) (mem g_s28_29 (|+->| NATURAL g_s10_11)) (mem g_s28_29 (perm g_s25_26)) (mem g_s29_31 (|-->| g_s25_26 g_s30_30)) (subset g_s31_32 g_s0_1) (mem g_s32_33 g_s0_1) (mem g_s32_33 g_s31_32) (not (mem g_s1_2 g_s31_32)) (= g_s31_32 (SET (mapplet g_s5_6 (mapplet g_s4_5 (mapplet g_s3_4 g_s2_3))))) (mem g_s33_34 (|+->| NATURAL g_s0_1)) (mem g_s33_34 (perm g_s31_32)) (mem g_s34_35 (|-->| g_s31_32 g_s30_30)) (subset g_s35_36 g_s6_7) (mem g_s36_37 g_s6_7) (mem g_s36_37 g_s35_36) (not (mem g_s7_8 g_s35_36)) (= g_s35_36 (SET (mapplet g_s9_10 g_s8_9))) (mem g_s37_38 (|+->| NATURAL g_s6_7)) (mem g_s37_38 (perm g_s35_36)) (mem g_s38_39 (|-->| g_s35_36 g_s30_30)) (subset g_s39_40 g_s11_12) (mem g_s40_41 g_s11_12) (mem g_s40_41 g_s39_40) (mem g_s41_42 g_s11_12) (not (mem g_s41_42 g_s39_40)) (mem g_s42_43 (|+->| NATURAL g_s11_12)) (mem g_s42_43 (perm g_s39_40)) (mem g_s43_44 (|+->>| g_s25_26 g_s31_32)) (mem g_s44_45 (|+->>| g_s25_26 g_s35_36)) (subset g_s45_46 g_s25_26) (= g_s46_47 NATURAL) (mem g_s47_49 (|-->| g_s46_47 g_s48_48)) (= (binary_inter (dom g_s43_44) (dom g_s44_45)) empty) (= (binary_inter (dom g_s44_45) g_s45_46) empty) (= (binary_union (binary_union (dom g_s43_44) (dom g_s44_45)) g_s45_46) g_s25_26)))
(define-fun |def_seext| () Bool true)
(define-fun |def_mchcst| () Bool true)
(define-fun |def_aprp| () Bool true)
(define-fun |def_abs| () Bool true)
(define-fun |def_inv| () Bool true)
(define-fun |def_ass| () Bool true)
(define-fun |def_sets| () Bool true)
(define-fun |def_imlprp| () Bool true)
(define-fun |def_imprp| () Bool true)
(define-fun |def_imext| () Bool true)
; PO group 0 
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_mchcst|)
(assert |def_aprp|)
(assert |def_imlprp|)
(assert |def_imprp|)
(assert |def_imext|)
(assert |def_seext|)
(assert |def_abs|)
(assert |def_inv|)
(assert |def_ass|)
(assert (= g_s50$1_51 g_s50_50))
(assert (= g_s51$1_53 g_s51_52))
(assert (= g_s52$1_55 g_s52_54))
(assert (= g_s53$1_57 g_s53_56))
(define-fun lh_1 () Bool (mem g_s54_58 g_s6_7))
(define-fun lh_2 () Bool (mem g_s54_58 g_s35_36))
(define-fun lh_3 () Bool (mem g_s18_19 g_s13_14))
; PO 1 in group 0
(assert (not (=> (and lh_1 lh_2 lh_3) (mem g_s20_21 g_s16_17))))
(check-sat)
(exit)