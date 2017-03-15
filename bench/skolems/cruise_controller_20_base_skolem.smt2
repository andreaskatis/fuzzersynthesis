(declare-fun $desiredSpeed$~1 () Real)
(declare-fun $desiredSpeed$2 () Real)
(declare-fun $mode$~1 () Int)
(declare-fun $OK$2 () Bool)

(assert (let ((a!1 (= 0.0 (ite true (to_real (div 0 10)) $desiredSpeed$~1))))
(let ((a!2 (or (not (ite true false (= $mode$~1 4))) a!1)))
  (and (= $OK$2 a!2) (= $desiredSpeed$2 0.0)))))
(check-sat)
