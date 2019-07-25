# Stores

Baker keeps the state of your `RecipeInstances` using a technique called event sourcing, such technique still requires
you to save data into a data store if you want to restore state or move it around. Baker's event sourcing uses 
[Akka's Persistence](https://doc.akka.io/docs/akka/current/persistence.html), and even though you don't need to know how
it works, we recommend understanding the implications of it, specially when it comes to configuring and choosing the underlying 
data store. 

The two main categories you have is local vs distributed, the former being used mainly for testing, and the latter for
production grade clusters, more specifically if you are going to use Baker on cluster mode, you NEED a distributed data store
for Baker to work as expected. We recommend the usage of Cassandra, since it is the store the team has tested and used on 
production.

## Configuration example of a local data store 

`application.conf`
```

```

## Configuration example of a distributed data store

`application.conf`
```

```
