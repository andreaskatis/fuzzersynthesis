; K = 0
; Transition relation
(define-fun T ((%init Bool) ($m$0 Bool) ($s$0 Bool) ($V27_dist$0 Int) ($OK$0 Bool) ($V33_env$0 Bool) ($V91_X$0 Bool) ($m$1 Bool) ($s$1 Bool) ($V27_dist$1 Int) ($OK$1 Bool) ($V33_env$1 Bool) ($V91_X$1 Bool)) Bool (and (= $OK$1 (=> $V33_env$1 (< $V27_dist$1 11))) (= $V33_env$1 (ite %init $V91_X$1 (and $V91_X$1 $V33_env$0))) (= $V91_X$1 (not (and $m$1 $s$1)))))
; Universally quantified variables
(declare-fun %init () Bool)
(declare-fun $m$~1 () Bool)
(declare-fun $s$~1 () Bool)
(declare-fun $V27_dist$~1 () Int)
(declare-fun $OK$~1 () Bool)
(declare-fun $V33_env$~1 () Bool)
(declare-fun $V91_X$~1 () Bool)
(declare-fun $m$0 () Bool)
(declare-fun $s$0 () Bool)
(declare-fun $V27_dist$0 () Int)
(declare-fun $OK$0 () Bool)
(declare-fun $V33_env$0 () Bool)
(declare-fun $V91_X$0 () Bool)
; Existentially quantified variables
; Assertions for universal part of the formula
(assert (T %init $m$~1 $s$~1 $V27_dist$~1 $OK$~1 $V33_env$~1 $V91_X$~1 $m$0 $s$0 $V27_dist$0 $OK$0 $V33_env$0 $V91_X$0))
