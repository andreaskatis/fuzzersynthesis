; K = 1
; Transition relation
(define-fun T ((%init Bool) ($m$0 Bool) ($s$0 Bool) ($V28_speed$0 Int) ($OK$0 Bool) ($V33_env$0 Bool) ($V90_X$0 Bool) ($m$1 Bool) ($s$1 Bool) ($V28_speed$1 Int) ($OK$1 Bool) ($V33_env$1 Bool) ($V90_X$1 Bool)) Bool (and (= $OK$1 (=> $V33_env$1 (< $V28_speed$1 4))) (= $V33_env$1 (ite %init $V90_X$1 (or $V90_X$1 $V33_env$0))) (= $V90_X$1 (not (and $m$1 $s$1)))))
; Universally quantified variables
(declare-fun $m$~1 () Bool)
(declare-fun $s$~1 () Bool)
(declare-fun $V28_speed$~1 () Int)
(declare-fun $OK$~1 () Bool)
(declare-fun $V33_env$~1 () Bool)
(declare-fun $V90_X$~1 () Bool)
(declare-fun $m$0 () Bool)
(declare-fun $s$0 () Bool)
(declare-fun $V28_speed$0 () Int)
(declare-fun $OK$0 () Bool)
(declare-fun $V33_env$0 () Bool)
(declare-fun $V90_X$0 () Bool)
; Existentially quantified variables
; Assertions for universal part of the formula
(assert (T true $m$~1 $s$~1 $V28_speed$~1 $OK$~1 $V33_env$~1 $V90_X$~1 $m$0 $s$0 $V28_speed$0 $OK$0 $V33_env$0 $V90_X$0))
