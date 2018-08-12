;;for vm_i in vms
(and
  (and
    (< (select vm_i "mem_size") 600 MB)
    (and
      (> (select vm_i "mem_size") 100 MB)
      (and
        (< (select vm_i "disk_size") 14 GB)
        (> (select vm_i "disk_size") 1 GB)
      )
    )
  )
  (and
    (> (select vm_i "num_cpus") 0)
    (< (select vm_i "num_cpus") 6)
  )
)
;;endfor

;;for vnf_i in vnfs
(and
  (and 
    (< (select vnf_i "address") 10.100.0.150 )
    (> (select vnf_i "address") 10.100.0.100 )
  )
  (and 
    (< (select vnf_i "nsh_aware") 1 )
    (and
      (> (select vnf_i "port") 1000)
      (< (select vnf_i "port") 10000)
    )
  )
)
;;endfor