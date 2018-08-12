;;------------------------
;;  VMS Setup
;;------------------------
(declare-const vms (Array Int (Array String Int)))
(declare-const props_vm1 (Array String Int))
(declare-const props_vm2 (Array String Int))
(declare-const props_vm3 (Array String Int))

(declare-const vms_size Int)
(assert (= vms_size 3))
;;------ Done VMS Setup ------

;;------------------------
;;  VMS Insert Values From Conf
;;------------------------
;; vm-name: VM2
(assert (= (store props_vm1 "mem_size" 512000000) props_vm1))
(assert (= (store props_vm1 "num_cpus" 2) props_vm1))
(assert (= (store props_vm1 "disk_size" 10000000000) props_vm1))
(assert (= (store vms 0 props_vm1) vms))

;; vm-name: VM1
(assert (= (store props_vm2 "mem_size" 512000000) props_vm2))
(assert (= (store props_vm2 "num_cpus" 2) props_vm2))
(assert (= (store props_vm2 "disk_size" 10000000000) props_vm2))
(assert (= (store vms 1 props_vm2) vms))

;; vm-name: VM3
(assert (= (store props_vm3 "mem_size" 512000000) props_vm3))
(assert (= (store props_vm3 "num_cpus" 2) props_vm3))
(assert (= (store props_vm3 "disk_size" 10000000000) props_vm3))
(assert (= (store vms 2 props_vm3) vms))

;;------ Done VMS Values ------

;;------------------------
;;  Networks Setup: 0, None detected
;;------------------------
(declare-const networks (Array Int (Array String Int)))
(declare-const networks_size Int)
(assert (= networks_size 0))


;;------------------------
;;  USER Rules
;;------------------------
;;for vm_i in vms | size: 3
(assert (forall ((x Int))
  (=>
    (and (< x vms_size) (> x -1))
    (and
      (< (select (select vms x) "mem_size") 700000000)
      (< (select (select vms x) "num_cpus") 3)
    )
  )
))

;;Ignore rules, because no networks descriptions where found!
;;for net_i in networks
;;    (<
;;      (select net_i "start_ip")
;;      (select net_i "end_ip")
;;    )
;;endfor

;;------ Done USER Rules ------

