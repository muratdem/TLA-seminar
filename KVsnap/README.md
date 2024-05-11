This repo contains a PlusCal specification of a key-value store with snapshot isolation. We also instantiate the `ClientCentric.tla` (from Tim Soethout's work) to be able to properly check the key-value store for snapshot isolation semantics. 
+ `KVsnap.tla` is the Pluscal model for the key-value store
+ `MCKVsnap.tla` is the file to use for TLC model checking
+ `MCKVsnap.cfg` is the corresponding config file for model checking (with this config, model checking completes under a minute; it is possible to add another key and model check)

If you uncomment the Serialization invariant in `KVsnap.tla`, and `MCKVsnap.cfg`, you can see a counterexample of how this snapshot-isolation key-value store violates serializability.

## Model checking with VSCode TLA+ plugin
+ Make sure TLA+ plugin is installed in VSCode
+ Open the .cfg file you are interested in checking in VSCode 
+ Get the VSCode panel (Option+X on Mac), and choose "TLA+: Check Model with TLC") 