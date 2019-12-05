# Running minikube locally

## Install docker
https://docs.docker.com/install/

##Install VirtualBox
https://www.virtualbox.org/wiki/Downloads

##Install Minikube
https://kubernetes.io/docs/tasks/tools/install-minikube/

##Create and start minikube cluster via VirtualBox
Execute `/baas-openshift-scripts/minikube/createMinikubeNamespace.sh`

##[Optional] Run minikube dashboard
Execute `minikube dashboard`

## Build example Docker images
`/examples/baas-minikube-setup/build-and-publish-images.sh`

##Deploy PODs to minikube
`kubectl apply -f /examples/baas-minikube-setup/baas-kubernetes-example.yml`