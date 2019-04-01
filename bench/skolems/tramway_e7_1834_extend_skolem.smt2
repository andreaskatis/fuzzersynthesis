(declare-fun $door_is_open$~1 () Bool)
(declare-fun $~flatten0$2 () Bool)
(declare-fun $V276_X$2 () Bool)
(declare-fun $V275_X$2 () Bool)
(declare-fun $V274_X$2 () Bool)
(declare-fun $V60_open_door$2 () Bool)
(declare-fun $V272_warning_start_cant_become_true_when_door_is_opening$2
             ()
             Bool)
(declare-fun $V270_warning_start_and_in_station_go_down_simultaneously$2
             ()
             Bool)
(declare-fun $V269_initially_not_in_station$2 () Bool)
(declare-fun $V268_door_initially_closed$2 () Bool)
(declare-fun $V266_door_doesnt_open_if_not_asked$2 () Bool)
(declare-fun $warning_start$0 () Bool)
(declare-fun $V59_prop_ok$2 () Bool)
(declare-fun $V252_X$2 () Bool)
(declare-fun $V61_close_door$2 () Bool)
(declare-fun $V253_between_A_and_X$2 () Bool)
(declare-fun $V273_X$~1 () Bool)
(declare-fun $OK$2 () Bool)
(declare-fun $V265_door_doesnt_close_if_not_asked$2 () Bool)
(declare-fun $V250_door_doesnt_open_out_of_station$2 () Bool)
(declare-fun $V253_between_A_and_X$~1 () Bool)
(declare-fun $V251_door_opens_before_leaving_station$2 () Bool)
(declare-fun $V276_X$~1 () Bool)
(declare-fun $~flatten0$~1 () Bool)
(declare-fun $V264_env_ok$2 () Bool)
(declare-fun $V273_X$2 () Bool)
(declare-fun $door_is_open$0 () Bool)
(declare-fun $request_door$~1 () Bool)
(declare-fun $V275_X$~1 () Bool)
(declare-fun $V62_door_ok$~1 () Bool)
(declare-fun $V58_env_always_ok$~1 () Bool)
(declare-fun $V267_tramway_doesnt_start_if_not_door_ok$2 () Bool)
(declare-fun $warning_start$~1 () Bool)
(declare-fun $V274_X$~1 () Bool)
(declare-fun $V58_env_always_ok$2 () Bool)
(declare-fun $V271_warning_start_only_in_station$2 () Bool)
(declare-fun $V252_X$~1 () Bool)
(declare-fun %init () Bool)
(declare-fun $in_station$0 () Bool)

(assert (let ((a!1 (not (and (not %init) (or (not $door_is_open$0) (not $V273_X$~1)))))
      (a!2 (not (and (not %init) (or (not $in_station$0) (not $V274_X$~1)))))
      (a!3 (= (and (not %init) (or (not $in_station$0) (not $V275_X$~1)))
              (and (not %init) (or (not $warning_start$0) (not $V276_X$~1)))))
      (a!4 (not (and (not %init) (or $warning_start$0 (not $warning_start$~1)))))
      (a!7 (and (not (and (not %init) $~flatten0$~1))
                (not %init)
                $V253_between_A_and_X$~1))
      (a!10 (not (ite true false (or (not $door_is_open$0) (not $V273_X$~1)))))
      (a!11 (not (ite true false (or (not $in_station$0) (not $V274_X$~1)))))
      (a!12 (= (ite true false (or (not $in_station$0) (not $V275_X$~1)))
               (ite true false (or (not $warning_start$0) (not $V276_X$~1)))))
      (a!13 (not (ite true false (or $warning_start$0 (not $warning_start$~1)))))
      (a!14 (not (ite %init false (or (not $door_is_open$0) (not $V273_X$~1)))))
      (a!15 (not (ite %init false (or (not $in_station$0) (not $V274_X$~1)))))
      (a!16 (= (ite %init false (or (not $in_station$0) (not $V275_X$~1)))
               (ite %init false (or (not $warning_start$0) (not $V276_X$~1)))))
      (a!17 (not (ite %init false (or $warning_start$0 (not $warning_start$~1)))))
      (a!20 (ite (ite %init
                      false
                      (and $request_door$~1 (not $warning_start$~1)))
                 true
                 (ite (ite %init false $~flatten0$~1)
                      false
                      (ite %init false $V253_between_A_and_X$~1))))
      (a!25 (not (and (not %init) (or $door_is_open$0 (not $door_is_open$~1)))))
      (a!29 (not (ite true false (or $door_is_open$0 (not $door_is_open$~1)))))
      (a!30 (not (ite %init false (or $door_is_open$0 (not $door_is_open$~1))))))
(let ((a!5 (and a!1
                (or a!2 (and (not %init) $V62_door_ok$~1))
                (or (not %init) (not $door_is_open$0))
                (or (not %init) (not $in_station$0))
                a!3
                (or (not $warning_start$0) $in_station$0)
                a!4))
      (a!6 (and a!1
                (or a!2 (and (not %init) $V62_door_ok$~1))
                (or (not %init) (not $door_is_open$0))
                (or (not %init) (not $in_station$0))
                a!3
                (or (not $warning_start$0) $in_station$0)
                a!4
                $V58_env_always_ok$~1))
      (a!8 (and (or (and (not %init) $request_door$~1 (not $warning_start$~1))
                    a!7)
                (not %init)
                (or (not $in_station$0) (not $V252_X$~1))))
      (a!18 (and (ite %init (not $in_station$0) true)
                 (ite %init (not $door_is_open$0) true)
                 true
                 (or false a!14)
                 (or (ite %init false $V62_door_ok$~1) a!15)
                 a!16
                 (or $in_station$0 (not $warning_start$0))
                 (or a!17 (not true))))
      (a!21 (and a!20
                 (ite %init false (or (not $in_station$0) (not $V252_X$~1)))))
      (a!26 (and a!1
                 a!25
                 (or a!2 (and (not %init) $V62_door_ok$~1))
                 (or (not %init) (not $door_is_open$0))
                 (or (not %init) (not $in_station$0))
                 a!3
                 (or (not $warning_start$0) $in_station$0)))
      (a!27 (and a!1
                 a!25
                 (or a!2 (and (not %init) $V62_door_ok$~1))
                 (or (not %init) (not $door_is_open$0))
                 (or (not %init) (not $in_station$0))
                 a!3
                 (or (not $warning_start$0) $in_station$0)
                 $V58_env_always_ok$~1))
      (a!31 (and (or $in_station$0 (not $warning_start$0))
                 a!16
                 (ite %init (not $in_station$0) true)
                 (ite %init (not $door_is_open$0) true)
                 (or (ite %init false $V62_door_ok$~1) a!15)
                 (or false a!14)
                 (or false a!30)
                 (or a!17 (not false)))))
(let ((a!9 (or (not (ite %init a!5 a!6))
               (and (or (not $door_is_open$0) $in_station$0) (not a!8))))
      (a!19 (ite %init
                 (and (ite true (not $in_station$0) true)
                      (ite true (not $door_is_open$0) true)
                      true
                      (or false a!10)
                      (or (ite true false $V62_door_ok$~1) a!11)
                      a!12
                      (or $in_station$0 (not $warning_start$0))
                      (or a!13 (not true)))
                 (and a!18 $V58_env_always_ok$~1)))
      (a!23 (= $V59_prop_ok$2
               (and (or $in_station$0 (not $door_is_open$0)) (not a!21))))
      (a!28 (or (not (ite %init a!26 a!27))
                (and (or (not $door_is_open$0) $in_station$0) (not a!8))))
      (a!32 (ite %init
                 (and (or $in_station$0 (not $warning_start$0))
                      a!12
                      (ite true (not $in_station$0) true)
                      (ite true (not $door_is_open$0) true)
                      (or (ite true false $V62_door_ok$~1) a!11)
                      (or false a!10)
                      (or false a!29)
                      (or a!13 (not false)))
                 (and a!31 $V58_env_always_ok$~1))))
(let ((a!22 (or (not a!19)
                (and (or $in_station$0 (not $door_is_open$0)) (not a!21))))
      (a!33 (or (and (or $in_station$0 (not $door_is_open$0)) (not a!21))
                (not a!32))))
(let ((a!24 (and (= $OK$2 a!22)
                 (= $V58_env_always_ok$2 a!19)
                 a!23
                 (= $V264_env_ok$2 a!18)
                 (= $V250_door_doesnt_open_out_of_station$2
                    (or $in_station$0 (not $door_is_open$0)))
                 (= $V251_door_opens_before_leaving_station$2 (not a!21))
                 (= $V253_between_A_and_X$2 a!20)
                 (= $V252_X$2 (not $in_station$0))
                 (= $V266_door_doesnt_open_if_not_asked$2 (or false a!14))
                 (= $V265_door_doesnt_close_if_not_asked$2 true)
                 (= $V267_tramway_doesnt_start_if_not_door_ok$2
                    (or (ite %init false $V62_door_ok$~1) a!15))
                 (= $V268_door_initially_closed$2
                    (ite %init (not $door_is_open$0) true))
                 (= $V269_initially_not_in_station$2
                    (ite %init (not $in_station$0) true))
                 (= $V270_warning_start_and_in_station_go_down_simultaneously$2
                    a!16)
                 (= $V271_warning_start_only_in_station$2
                    (or $in_station$0 (not $warning_start$0)))
                 (= $V272_warning_start_cant_become_true_when_door_is_opening$2
                    (or a!17 (not true)))
                 (= $V60_open_door$2 true)
                 (= $V273_X$2 (not $door_is_open$0))
                 (= $V61_close_door$2 false)
                 (= $V274_X$2 (not $in_station$0))
                 (= $V275_X$2 (not $in_station$0))
                 (= $V276_X$2 (not $warning_start$0))
                 (= $~flatten0$2 (ite %init false $door_is_open$~1))))
      (a!34 (and (= $OK$2 a!33)
                 (= $V58_env_always_ok$2 a!32)
                 a!23
                 (= $V264_env_ok$2 a!31)
                 (= $V250_door_doesnt_open_out_of_station$2
                    (or $in_station$0 (not $door_is_open$0)))
                 (= $V251_door_opens_before_leaving_station$2 (not a!21))
                 (= $V253_between_A_and_X$2 a!20)
                 (= $V252_X$2 (not $in_station$0))
                 (= $V266_door_doesnt_open_if_not_asked$2 (or false a!14))
                 (= $V265_door_doesnt_close_if_not_asked$2 (or false a!30))
                 (= $V267_tramway_doesnt_start_if_not_door_ok$2
                    (or (ite %init false $V62_door_ok$~1) a!15))
                 (= $V268_door_initially_closed$2
                    (ite %init (not $door_is_open$0) true))
                 (= $V269_initially_not_in_station$2
                    (ite %init (not $in_station$0) true))
                 (= $V270_warning_start_and_in_station_go_down_simultaneously$2
                    a!16)
                 (= $V271_warning_start_only_in_station$2
                    (or $in_station$0 (not $warning_start$0)))
                 (= $V272_warning_start_cant_become_true_when_door_is_opening$2
                    (or a!17 (not false)))
                 (= $V60_open_door$2 false)
                 (= $V273_X$2 (not $door_is_open$0))
                 (= $V61_close_door$2 false)
                 (= $V274_X$2 (not $in_station$0))
                 (= $V275_X$2 (not $in_station$0))
                 (= $V276_X$2 (not $warning_start$0))
                 (= $~flatten0$2 (ite %init false $door_is_open$~1)))))
  (ite a!9 a!24 (ite a!28 a!34 true))))))))
(check-sat)
