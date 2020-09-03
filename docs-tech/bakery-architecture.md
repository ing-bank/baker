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
A Cassandra persistence backend can be configured to keep the state of the recipe instances and a Kafka 
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

## Bakery Controller

The Bakery Controller follows Kubernete's general architecture pattern called [Controller Pattern](https://kubernetes.io/docs/concepts/architecture/controller/)
It is deployed as a single pod which uses Kubernete's API to watch the Baker and Interaction [Custom Resources](https://kubernetes.io/docs/concepts/extend-kubernetes/api-extension/custom-resources/), which have the
specification of the Baker clusters and Interactions to be deployed. The Baker Controller constantly watches for creation,
changes and deletions of such Custom Resources, so that the state of the namespace always matches the textual specifications.

The Bakery Controller also creates Kubernetes ConfigMaps which we call "Manifests", which are outcome of the creation of
a Custom Resource, these are config maps used as internal mechanisms to expose semantic data about the deployed components, more of
that in the following section.

## Baker and Interaction Custom Resources

The 2 Custom Resources that we have contain all the requirements of the components to be deployed, like the number of cluster nodes 
/ replicas, the encoded recipes to be added to the Baker cluster nodes, or the docker images to be used for interactions.

For Kubernetes to understand the Bakery Custom Resources, one must first `kubectl apply -f` the Custom Resource Definitions which
work as specifications.

* [crd-baker.yaml](../bakery-integration-tests/src/test/resources/kubernetes/crd/crd-baker.yaml)
* [crd-interaction.yaml](../bakery-integration-tests/src/test/resources/kubernetes/crd/crd-interaction.yaml)

The Bakery Controller can be configured to use ConfigMaps instead of Custom Resources in case you are not able to use Custom Resources in your cluster
by adding `bakery-controller.use-crds = false` to the `application.conf` of the controller.

An example of Custom Resource can be found [here for a Baker](../bakery-integration-tests/src/test/resources/kubernetes/crd/baker-webshop.yaml)
and [here for an interaction](../bakery-integration-tests/src/test/resources/kubernetes/crd/interactions-example.yaml)

Also the specification of the Custom Resources can be found [here for Baker](../bakery-integration-tests/src/test/resources/kubernetes/crd/crd-baker.yaml)
and [here for Interaction](../bakery-integration-tests/src/test/resources/kubernetes/crd/crd-interaction.yaml)

### Baker Manifests

The Baker manifest is a Kubernetes ConfigMap created by the Bakery Controller from a Baker Custom Resource. 

The controller uses the manifest to mount the recipes that go into the Baker clusters. For every Baker manifest there
exists one Baker cluster. 

The naming pattern of the manifests is: `<name-in-the-cr>-manifest`, and they are labeled `bakery-manifest: recipes`.

It is possible to use them to inspect the recipes deployed in the namespace.

### Interaction Manifests

The Interaction manifest is created by the Bakery Controller after deploying an interaction from the specification of an
Interaction Custom Resource. 

The controller uses the HTTP api of the deployed interaction to request for the data structure that specifies
all the interfaces of the interactions within the Interaction replicas to aggregate them into the 
manifest. 

The naming pattern of the manifests is: `<name-in-the-cr>-manifest`, and they are labeled `bakery-manifest: interactions`.

The Baker clusters use the Kubernetes API to query for all available interactions in the namespace (by querying 
ConfigMaps with the label `bakery-manifest: interactions`), effectively working as a service discovery mechanism.

## Baker Akka Clusters

When a Baker Custom Resource is created in the namespace, the Bakery Controller creates a Kubernetes Deployment and Service, the deployed
Pods contain an Akka cluster node which keep the state of the Baker recipe instances and persists them into a Cassandra database.

It exposes the Baker http api, which is accessible from the Kubernetes Service, and it uses the Kubernetes api to discover
available interactions in the namespace by querying for ConfigMaps with the corresponding interaction manifest label
`bakery-manifest: interactions`.

## Interactions

When an Interaction Custom Resource is created in the namespace, the Bakery Controller creates a Kubernetes Deployment and Service,
the Pods that come out from the Deployment use the docker image specified at the Interaction Custom Resource to load 
the implementations of the interactions. 

The docker image used by the Interaction replicas must be built using the `bakery-interaction` [library](), which adds the required 
http api layer to the interaction implementation from which the Bakery Controller can extract the implementations interface 
for the manifest and from which the Baker clusters can request the execution of an interaction given some ingredients.

We have built an [sbt plugin]() and a [maven plugin]() to easily built such docker image.

## Configuration mounting

As part of the Custom Resources of both Bakers and Interactions, one can add the name of a secret and/or a ConfigMap to mount configuration
within the Bakers and Interaction pods, this is used for example to configure per environment Cassandra connectivity or 
specific configuration required by the interaction implementations. Alternatively the Custom Resource interface allows for environment 
variable configuration at the Custom Resource level.

## Baker Clients

Baker clients can either consume the http api or use our published `bakery-baker-client` library to use a Baker scala/java 
api as you would normally use the Baker library.

The http api exposed by Baker cluster Services is without authentication and authorization, an extra system must be 
implemented on the environment, as well as expose it using Kubernetes Routes, for example within the ING Bakery
we use extra authentication/authorization systems to let our users access our https endpoints exposed by Routes which
follow ING standards.
