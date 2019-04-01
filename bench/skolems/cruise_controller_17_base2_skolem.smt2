(declare-fun $cruiseThrottle$3 () Real)
(declare-fun $mode$3 () Int)
(declare-fun $cruiseThrottle$0 () Real)
(declare-fun $OK$3 () Bool)

(assert (let ((a!1 (= 0.0 (ite false (to_real (div 0 10)) $cruiseThrottle$0))))
(let ((a!2 (= $OK$3 (or (not (= 5 4)) a!1))))
  (and a!2 (= $mode$3 5) (= $cruiseThrottle$3 0.0)))))
(check-sat)
