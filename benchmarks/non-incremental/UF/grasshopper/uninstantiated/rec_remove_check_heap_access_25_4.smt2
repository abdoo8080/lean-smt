(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sl/rec_remove.spl:25:4-19:Possible heap access through null or dangling reference
  |)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun ep$0 (FldLoc SetLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun Frame$0 (SetLoc SetLoc FldLoc FldLoc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Alloc_1$0 () SetLoc)
(declare-fun Axiom$0 () Bool)
(declare-fun Axiom_1$0 () Bool)
(declare-fun Axiom_2$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst$0 () Loc)
(declare-fun n1_2$0 () Loc)
(declare-fun n2_2$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_1$0 () FldLoc)
(declare-fun nondet_1$0 () Bool)
(declare-fun sk_?X_9$0 () SetLoc)
(declare-fun sk_?X_10$0 () SetLoc)
(declare-fun sk_?X_11$0 () SetLoc)
(declare-fun t$0 () Loc)
(declare-fun t_1$0 () Loc)
(declare-fun t_2$0 () Loc)
(declare-fun t_3$0 () Loc)
(declare-fun t_4$0 () Loc)

(assert (= (ep$0 next$0 FP_1$0 n2_2$0) t_4$0))

(assert (= (ep$0 next$0 FP_1$0 n1_2$0) t_3$0))

(assert (= (ep$0 next$0 FP_1$0 lst$0) t_2$0))

(assert (= (ep$0 next$0 FP_1$0 null$0) t_1$0))

(assert (= (read$0 next_1$0 lst$0) t$0))

(assert (forall ((?f FldLoc)) (= (read$0 ?f null$0) null$0)))

(assert (forall ((x Loc) (y Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$0 x X) (in$0 x (setminus$0 X Y)) (not (in$0 x Y)))
            (and (or (in$0 x Y) (not (in$0 x X)))
                 (not (in$0 x (setminus$0 X Y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$0 x X) (in$0 x Y) (in$0 x (intersection$0 X Y)))
            (and (or (not (in$0 x X)) (not (in$0 x Y)))
                 (not (in$0 x (intersection$0 X Y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$0 x (union$0 X Y)) (or (in$0 x X) (in$0 x Y)))
            (and (not (in$0 x X)) (not (in$0 x Y))
                 (not (in$0 x (union$0 X Y)))))))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or (Btwn$0 next$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_11$0 next$0 lst$0 null$0))))

(assert (or (Btwn$0 next_1$0 n2_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_9$0 next_1$0 n2_2$0 null$0))))

(assert (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (Frame$0 FP_1$0 Alloc$0 next$0 next_1$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= sk_?X_9$0 (lseg_domain$0 next_1$0 n2_2$0 null$0)))

(assert (= sk_?X_10$0 FP_1$0))

(assert (= FP$0 (union$0 FP_1$0 FP$0)))

(assert (= sk_?X_11$0 FP$0))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (not (= lst$0 null$0)))

(assert (not (in$0 null$0 Alloc_1$0)))

(assert (not nondet_1$0))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 n1_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 n1_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 n1_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 n1_2$0 null$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) ?y) (not (Btwn$0 ?f ?x ?y ?y))
            (not (in$0 ?y ?X)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (in$0 ?y ?X))
            (in$0 (ep$0 ?f ?X ?x) ?X))))

(assert (or (and Axiom_2$0 Axiom_1$0 Axiom$0)
    (not (Frame$0 FP_1$0 Alloc$0 next$0 next_1$0))))

(assert (or (Btwn$0 next$0 n1_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_10$0 next$0 n1_2$0 null$0))))

(assert (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc_1$0 FP_1$0)
      (setminus$0 Alloc_1$0 Alloc$0)))))

(assert (= n1_2$0 (read$0 next$0 lst$0)))

(assert (= Alloc_1$0 (union$0 FP_2$0 Alloc_1$0)))

(assert (= sk_?X_9$0
  (union$0 (intersection$0 Alloc_1$0 FP_1$0) (setminus$0 Alloc_1$0 Alloc$0))))

(assert (lseg_struct$0 sk_?X_9$0 next_1$0 n2_2$0 null$0))

(assert (= sk_?X_10$0 (lseg_domain$0 next$0 n1_2$0 null$0)))

(assert (lseg_struct$0 sk_?X_10$0 next$0 n1_2$0 null$0))

(assert (= sk_?X_11$0 (lseg_domain$0 next$0 lst$0 null$0)))

(assert (lseg_struct$0 sk_?X_11$0 next$0 lst$0 null$0))

(assert (not (in$0 null$0 Alloc$0)))

(assert (not (in$0 lst$0 FP_2$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_1$0 n2_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_1$0 n2_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_1$0 n2_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_1$0 n2_2$0 null$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (or (in$0 (ep$0 ?f ?X ?x) ?X) (= ?x (ep$0 ?f ?X ?x)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) (ep$0 ?f ?X ?x))))

(assert (or (not Axiom$0)
    (forall ((?x Loc) (?y Loc) (?z Loc))
            (or (in$0 ?x FP_1$0)
                (and (Btwn$0 next$0 ?x ?z ?y) (Btwn$0 next_1$0 ?x ?z ?y))
                (and (not (Btwn$0 next$0 ?x ?z ?y))
                     (not (Btwn$0 next_1$0 ?x ?z ?y)))
                (not (= ?x (ep$0 next$0 FP_1$0 ?x)))))))

(assert (or (not Axiom_1$0)
    (forall ((?x Loc) (?y Loc) (?z Loc))
            (or (and (Btwn$0 next$0 ?x ?z ?y) (Btwn$0 next_1$0 ?x ?z ?y))
                (and (not (Btwn$0 next$0 ?x ?z ?y))
                     (not (Btwn$0 next_1$0 ?x ?z ?y)))
                (not
                     (or (Btwn$0 next$0 ?x ?y (ep$0 next$0 FP_1$0 ?x))
                         (and (Btwn$0 next$0 ?x ?y ?y)
                              (not
                                   (Btwn$0 next$0 ?x (ep$0 next$0 FP_1$0 ?x)
                                     (ep$0 next$0 FP_1$0 ?x))))))))))

(assert (or (not Axiom_2$0)
    (forall ((?x Loc))
            (or (= (read$0 next$0 ?x) (read$0 next_1$0 ?x))
                (not (in$0 ?x (setminus$0 Alloc$0 FP_1$0)))))))

(assert (forall ((?f FldLoc) (?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?z)) (not (Btwn$0 ?f ?x ?u ?y))
            (and (Btwn$0 ?f ?x ?u ?z) (Btwn$0 ?f ?u ?y ?z)))))

(assert (forall ((?f FldLoc) (?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?z)) (not (Btwn$0 ?f ?y ?u ?z))
            (and (Btwn$0 ?f ?x ?y ?u) (Btwn$0 ?f ?x ?u ?z)))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (Btwn$0 ?f ?y ?z ?z))
            (Btwn$0 ?f ?x ?z ?z))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?z))
            (and (Btwn$0 ?f ?x ?y ?y) (Btwn$0 ?f ?y ?z ?z)))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (Btwn$0 ?f ?x ?z ?z))
            (Btwn$0 ?f ?x ?y ?z) (Btwn$0 ?f ?x ?z ?y))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (= ?x ?y)
            (Btwn$0 ?f ?x (read$0 ?f ?x) ?y))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc))
        (or (not (= (read$0 ?f ?x) ?x)) (not (Btwn$0 ?f ?x ?y ?y)) (= ?x ?y))))

(assert (forall ((?f FldLoc) (?x Loc)) (Btwn$0 ?f ?x (read$0 ?f ?x) (read$0 ?f ?x))))

(assert (forall ((?f FldLoc) (?x Loc)) (Btwn$0 ?f ?x ?x ?x)))

(check-sat)
(exit)
