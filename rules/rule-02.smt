;;for vm_i in vms
(and
  (< (select vm_i "mem_size") 600 MB)
  (< (select vm_i "num_cpus") 6)
)
;;endfor