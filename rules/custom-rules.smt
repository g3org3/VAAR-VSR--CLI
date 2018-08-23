;; deftype containers tosca.nodes.ETSO.K8s.Container

;;for container in containers
(and
  (= (select container "replicas") 4)
  (= (select container "service_type") 'LoadBalancer')
)
;;endfor