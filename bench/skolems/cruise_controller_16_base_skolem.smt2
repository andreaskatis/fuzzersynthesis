(declare-fun $desiredSpeed$2 () Real)
(declare-fun $mode$2 () Int)
(declare-fun $OK$2 () Bool)

(assert (and (= $OK$2 true) (= $mode$2 7) (= $desiredSpeed$2 0.0)))
(check-sat)
