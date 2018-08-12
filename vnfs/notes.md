VNF:
virtual network function
tosca_definitions_version:
   This defines the TOSCA definition version on which the template is based.
   The current version being tosca_simple_profile_for_nfv_1_0_0.

tosca_default_namespace:
   This is optional. It mentions default namespace which includes schema,
   types version etc.

description:
   A short description about the template.

metadata:
   template_name: A name to be given to the template.
A VNF includes VDU/s, connection point/s and virtual link/s.
Hence a valid VNFD must have these 3 components
topology_template:
   Describes the topology of the VNF under node_template field.
   node_template:
       Describes node types of a VNF.
       VDU:
           Describes properties and capabilities of Virtual Deployment
           Unit.
       CP:
           Describes properties and capabilities of Connection Point.
       VL:
           Describes properties and capabilities of Virtual Link.

node_types:
  tosca.nodes.nfv.VDU.Tacker:
    derived_from: tosca.nodes.nfv.VDU
    capabilities:
      nfv_compute:
        type: tosca.datatypes.compute_properties
    properties:
      name:
        type: string
        required: false