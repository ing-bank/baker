# Configure

Here you will find the `reference.conf` of Baker, this represents the current default configuration of Baker.

_Note: Since the Baker runtime is based on Akka, there is extra configuration that can be done, please refer to the
[Akka configuration documentation](https://doc.akka.io/docs/akka/current/general/configuration.html)_

```

baker {

  actor {
    # the id of the journal to read events from
    read-journal-plugin = "inmemory-read-journal"

    # either "local" or "cluster-sharded"
    provider = "local"

    # the recommended nr is number-of-cluster-nodes * 10
    cluster.nr-of-shards = 50

    # the time that inactive actors (processes) stay in memory
    idle-timeout = 5 minutes

    # The interval that a check is done of processes should be deleted
    retention-check-interval = 1 minutes
  }

  # the default timeout for Baker.bake(..) process creation calls
  bake-timeout = 10 seconds

  # the timeout for refreshing the local recipe cache
  process-index-update-cache-timeout = 5 seconds

  # the default timeout for Baker.processEvent(..)
  process-event-timeout = 10 seconds

  # the default timeout for inquires on Baker, this means getIngredients(..) & getEvents(..)
  process-inquire-timeout = 10 seconds

  # when baker starts up, it attempts to 'initialize' the journal connection, this may take some time
  journal-initialize-timeout = 30 seconds

  # the default timeout for adding a recipe to Baker
  add-recipe-timeout = 10 seconds

  # the time to wait for a gracefull shutdown
  shutdown-timeout = 30 seconds

  # The ingredients that are filtered out when getting the process instance.
  # This should be used if there are big ingredients to improve performance and memory usage.
  # The ingredients will be in the ingredients map but there value will be an empty String.
  filtered-ingredient-values = []

  # encryption settings
  encryption {

    # whether to encrypt data stored in the journal, off or on
    enabled = off

    # if enabled = on, a secret should be set
    # secret = ???
  }
}

akka {

  # by default we use the in memory journal from: https://github.com/dnvriend/akka-persistence-inmemory
  persistence.journal.plugin = "inmemory-journal"
  
  persistence.snapshot-store.plugin = "inmemory-snapshot-store"
}

```