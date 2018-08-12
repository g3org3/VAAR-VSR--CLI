;;for vm_i in vms
(and
  (< (select vm_i "mem_size") 500 MB)
  (< (select vm_i "num_cpus") 3)
)
;;endfor

;;for net_i in networks
(<
  (select net_i "start_ip")
  (select net_i "end_ip")
)
;;endfor
