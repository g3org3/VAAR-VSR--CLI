(declare-const vms (Array Int (Array String Int)))
(declare-const props_vm1 (Array String Int))
(declare-const props_vm2 (Array String Int))
(declare-const props_vm3 (Array String Int))
(declare-const networks (Array Int (Array String Int)))
(declare-const props_net1 (Array String Int))

(declare-const vms_size Int)
(declare-const networks_size Int)

(assert (= (store props_net1 "start_ip" 3232235570) props_net1))
(assert (= (store props_net1 "end_ip" 3232235720) props_net1))
(assert (= (store networks 0 props_net1) networks))

(assert (= (store props_vm1 "cpus" 8) props_vm1))
(assert (= (store props_vm1 "mem_size" 512000000) props_vm1))
(assert (= (store props_vm1 "disk_size" 10000000) props_vm1))
(assert (= (store vms 0 props_vm1) vms))

(assert (= (store props_vm2 "cpus" 9) props_vm2))
(assert (= (store props_vm2 "mem_size" 600000000) props_vm2))
(assert (= (store props_vm2 "disk_size" 10000000000) props_vm2))
(assert (= (store vms 1 props_vm2) vms))

(assert (= (store props_vm3 "cpus" 9) props_vm3))
(assert (= (store props_vm3 "mem_size" 600000000) props_vm3))
(assert (= (store props_vm3 "disk_size" 10000000000) props_vm3))
(assert (= (store vms 2 props_vm3) vms))

(assert (= vms_size 3))
(assert (= networks_size 1))

(assert (forall ((x Int))
  (=>
    (and (< x vms_size) (> x -1))
    (and
      (< (select (select vms x) "cpus") 10)
      (< (select (select vms x) "mem_size") 700000000)
    )
  )
))


(assert (forall ((net Int))
  (=>
    (and (< net networks_size) (> net -1))
    (<
      (select (select networks net) "start_ip")
      (select (select networks net) "end_ip")
    )
  )
))

;; (check-sat)
