;;deftype vms tosca.nodes.nfv.VDU
;;for vm in vms
  (< vm.mem_size 100 GB)
;;endfor

;;for fp in fps
  (= fp.policy 'example_policy')
  ;;for cap in fp.forwarder.capability
    (= cap 'CP21')
  ;;endfor
;;endfor

;; RAW
;; fp.forwarder.capability
(assert (forall ((x Int))
  (=>
    (and (< x fps.forwarder.capabilities_size) (> x -1))
    (forall ((y Int))
      (=>
        (and (< y (select fps.forwarder.capabilities_sizes x)) (> y -1))
        (= (select (select fps.forwarder.capabilities x) y) 'CP21')
      )
    )
  )
))