;; deftype vdus tosca.nodes.nfv.VDU.Tacker
;; deftype cps tosca.nodes.nfv.CP.Tacker

;;for vm_i in vdus
(= (select vm_i "flavor") 'm1.medium')
;;endfor

;;for cpi in cps
(and
  (< (select cpi "management") 1)
  (> (select cpi "management") -1)
)
;;endfor