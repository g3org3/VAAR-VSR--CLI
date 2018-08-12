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
(assert (= (store props_vm1 "mem_size" 512000000) props_vm1));; var.id: 0
(assert (= (store props_vm1 "num_cpus" 2) props_vm1));; var.id: 1
(assert (= (store vms 0 props_vm1) vms))

;; vm-name: VM1
;; (assert (= (store props_vm2 "mem_size" 900000000) props_vm2));; var.id: 2
(assert (= (store props_vm2 "num_cpus" 2) props_vm2));; var.id: 3
(assert (= (store vms 1 props_vm2) vms))

;; vm-name: VM3
(assert (= (store props_vm3 "mem_size" 512000000) props_vm3));; var.id: 4
(assert (= (store props_vm3 "num_cpus" 2) props_vm3));; var.id: 5
(assert (= (store vms 2 props_vm3) vms))

;;------ Done VMS Values ------

;;------------------------
;;  VNFS Setup
;;------------------------
(declare-const vnfs (Array Int (Array String Int)))
(declare-const props_vnf1 (Array String Int))
(declare-const props_vnf2 (Array String Int))
(declare-const props_vnf3 (Array String Int))

(declare-const vnfs_size Int)
(assert (= vnfs_size 3))
;;------ Done VNFS Setup ------

;;------------------------
;;  VNFS Insert Values From Conf
;;------------------------
;; vnf-name: VNF2
(assert (= (store props_vnf1 "address" 174325866) props_vnf1));; var.id: 6
;; (assert (= (store props_vnf1 "nsh_aware" 1) props_vnf1));; var.id: 7
(assert (= (store vnfs 0 props_vnf1) vnfs))

;; vnf-name: VNF3
(assert (= (store props_vnf2 "address" 174325867) props_vnf2));; var.id: 8
;; (assert (= (store props_vnf2 "nsh_aware" 1) props_vnf2));; var.id: 9
(assert (= (store vnfs 1 props_vnf2) vnfs))

;; vnf-name: VNF1
(assert (= (store props_vnf3 "address" 174325865) props_vnf3));; var.id: 10
;; (assert (= (store props_vnf3 "nsh_aware" 1) props_vnf3));; var.id: 11
(assert (= (store vnfs 2 props_vnf3) vnfs))

;;------ Done VNFS Values ------

;;------------------------
;;  NETWORKS Setup: 0, None detected
;;------------------------
(declare-const networks (Array Int (Array String Int)))
(declare-const networks_size Int)
(assert (= networks_size 0))
;;------------------------
;;  CPS Setup
;;------------------------
(declare-const cps (Array Int (Array String Int)))
(declare-const props_cp1 (Array String Int))
(declare-const props_cp2 (Array String Int))
(declare-const props_cp3 (Array String Int))
(declare-const props_cp4 (Array String Int))

(declare-const cps_size Int)
(assert (= cps_size 4))
;;------ Done CPS Setup ------

;;------------------------
;;  CPS Insert Values From Conf
;;------------------------
;; cp-name: CP41
(assert (= (store cps 0 props_cp1) cps))

;; cp-name: CP31
(assert (= (store cps 1 props_cp2) cps))

;; cp-name: CP21
(assert (= (store cps 2 props_cp3) cps))

;; cp-name: CP11
(assert (= (store cps 3 props_cp4) cps))

;;------ Done CPS Values ------



;;------------------------
;;  USER Rules
;;------------------------
;;for vm_i in vms | size: 3
(assert (forall ((x Int))
  (=>
    (and (< x vms_size) (> x -1))
    (and
      (< (select (select vms x) "mem_size") 600000000)
      (and
        (> (select (select vms x) "num_cpus") 0)
        (< (select (select vms x) "num_cpus") 6)
      )
    )
  )
))

;;for vnf_i in vnfs | size: 3
(assert (forall ((x Int))
  (=>
    (and (< x vnfs_size) (> x -1))
    (and
      (and 
        (<
          (select (select vnfs x) "address")
          174325910
        )
        (> (select (select vnfs x) "address")
          174325860
        )
      )
      (< 
        (select (select vnfs x) "nsh_aware")
        1
      )
    )
  )
))

;;------ Done USER Rules ------

