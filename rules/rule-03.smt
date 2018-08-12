;;for vm_i in vms
(and
  (< (select vm_i "mem_size") 600 MB)
  (and
    (> (select vm_i "num_cpus") 0)
    (< (select vm_i "num_cpus") 6)
  )
)
;;endfor

;;for vnf_i in vnfs
(< 
  (select vnf_i "nsh_aware")
  1
)
;;endfor