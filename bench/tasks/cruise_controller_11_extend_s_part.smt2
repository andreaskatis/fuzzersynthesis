; K = 0
; Transition relation
(define-fun T ((%init Bool) ($mode$0 Int) ($cruiseThrottle$0 Real) ($OK$0 Bool) ($mode$1 Int) ($cruiseThrottle$1 Real) ($OK$1 Bool)) Bool (= $OK$1 (or (or (or (= $mode$1 4) (= $mode$1 5)) (= $mode$1 6)) (= $cruiseThrottle$1 (/ 0 10)))))
; Universally quantified variables
(declare-fun %init () Bool)
(declare-fun $mode$~1 () Int)
(declare-fun $cruiseThrottle$~1 () Real)
(declare-fun $OK$~1 () Bool)
(declare-fun $mode$0 () Int)
(declare-fun $cruiseThrottle$0 () Real)
(declare-fun $OK$0 () Bool)
(assert (T %init $mode$~1 $cruiseThrottle$~1 $OK$~1 $mode$0 $cruiseThrottle$0 $OK$0))
