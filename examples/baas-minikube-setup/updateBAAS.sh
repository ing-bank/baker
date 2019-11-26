set -eo pipefail
set -o nounset
#set -o xtrace

projectRoot=`pwd`

# clean up first
app_name=baas
app_context=baas
app_name_lower=`echo $app_name | awk '{print tolower($0)}'`
image_name=apollo.docker.ing.net/${app_name_lower}
namespace_name=default
targetDir=${projectRoot}/.target


if [ -d "$targetDir" ]; then rm -Rf $targetDir; fi

mkdir "$targetDir"


function log () {
  echo -e "\n $1 \n"
}

log "Delete current deployments"
set +e
kubectl delete deployment $app_name_lower --namespace=$namespace_name | echo "Ignoring deletion of non existed"
set -e

#TODO: build images

log "Check status of Minikube & start if stopped"

mini_running=$(minikube status | grep 'host:' | awk '{print $2}')

echo $mini_running

if [[ $mini_running == "Stopped" ]]
  then
    sh ./createMinikubeNamespace.sh
    echo "Started minikube"
fi

log "Set to minikube env"

eval $(minikube docker-env)
kubectl config use-context minikube

log "Remove old image"
docker rmi $app_name_lower --force || echo "Ignoring docker proxy error"

log "Build new image"
# make sure minikube can access registry run : minikube delete  && minikube start --insecure-registry=registry-all.docker.ing.net

# Build baas example images
# Assuming current working directory is: ../baker/examples/baas-minikube-setup
cd ../..
sbt baas-node-state/docker:publish
sbt baas-client-example/docker:publish
sbt baas-interactions-example/docker:publish
sbt baas-event-listener-example/docker:publish

cd examples/baas-minikube-setup

kubectl apply -f akka-cluster.yml




