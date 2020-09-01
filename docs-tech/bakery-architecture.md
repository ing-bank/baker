# Bakery High Level Architecture

![Architecture diagram](./Bakery%20Architecture.png)

### Bakery Controller

The bakery controller is the first and only component that needs to be initially manually installed, its
responsibility is to keep the state of bakery consistent with the specifications provided. For each 
baker specification, the bakery controller makes sure it exists a cluster that will keep and orchestrate
the recipes within the specification; as well for interactions, for each specification of an interaction
it makes sure it exists at all time enough instances of the interaction to serve the baker clusters.

#### Baker Specs

A baker specification is a textual definition of a baker cluster to be deployed by the bakery controller.
When created the bakery controller will create the cluster, when updated the bakery controller will 
update the cluster accordingly, and finally when deleted the cluster will as well be deleted.
Within one can find the name, expected cluster size, configuration and most importantly one or more base64 
encoded baker recipes to be loaded into the baker cluster.

#### Interaction Specs

An interaction specification is a textual definition of an interaction to be deployed by the bakery controller.
When created the bakery controller will create the replicas, when updated the bakery controller will 
update the replicas accordingly, and finally when deleted the replicas will as well be deleted.
Within one can find the name, amount of replicas, configuration and docker image to be used to load the 
interaction functionality into the interaction replicas.

### Baker Clusters

A baker cluster is created on demand by the bakery controller, it will be initially loaded with the required
baker recipes, it uses a service discovery mechanism to locate the interactions required by the recipes and
it exposes all the baker operations through an http api. When an interaction of the recipe is fired, the baker
cluster node will use the discovered interaction service to send the ingredients through an http api to a load
balanced interaction replica, which will compute the interaction and return the correspondent output event. 
A cassandra persistence backend can be configured to keep the state of the recipe instances and a Kafka 
producer to publish the baker events.

### Interaction Replicas

A set of interaction replicas is created on demand by the bakery controller, each instance comes with the 
implementation of a set of interactions, they expose the interaction name and ingredient interface through
http, which the bakery controller uses to enable the service discovery mechanism used by baker clusters to
discover the locations of the interactions they require. The interaction instance also exposes an http api
to "apply" or request the execution of an interaction given the required set of ingredients, such api is 
used by the baker clusters when they require to fire an interaction.
Interactions might access external services for their functionality, or they might contain no "side-effects"
and are pure computations, which traditionally are called "sieves".

### Baker Clients

A library to be included within the consumers of bakery, to ease the integration of old and new baker users. 
It exposes the traditional baker java and scala api, but within its implementation it requests through http 
to the exposed baker clusters. One instance of the client is created per baker cluster.


# Bakery Kubernetes Implementation

![Kubernetes diagram](./Bakery%20Kubernetes%20Architecture.png)

# Bakery Controller

# Baker and Interaction CRDs

## Baker Manifests

## Interaction Manifests

# Baker Akka Clusters

# Interactions

# Configuration mounting
