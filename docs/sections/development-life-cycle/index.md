# Development Life Cycle

In this section we will explain every step in the process of developing business functionality across your microservices using Baker, we will focus on practical aspects: how to do things and why you should do them. The general steps in the development lifecycle are:

1) Design a Recipe: In Baker you are always required to make a distinction between specification (Recipe) and implementation (Runtime) of your business process, you will use the Recipe DSL to express the interface of ingredients and events (data) and interactions (actions), which will help Baker understand your orchestration flow. Baker recipes are the interface of your business process, they specify Baker Types without values for Ingredients and Events, and specify input Ingredients and output Events without implementation for Interactions. 
2) Use Visualizations: Baker is able to create a graphical representation of your recipe, this becomes very useful for reasoning about your business process, and easily communicate and discuss about it.
3) Implement Interactions: To execute the orchestration plan specified by the recipe, you must create interaction implementations, which are the code blocks that match the interfaces of the ingredient/event/interactions. These must be registered to baker, which will imply their correspondence with the recipe by matching the interfaces.
4) Create Process Instances, Fire Events and Inquiry: After registering recipes and implementations, you are able to create instances of the recipes, which execute after you fire events, which will execute calls to your microservices. The state of a given process may be requested at any time for application utility.
5) Test: Common methods of testing are, independently test each implementation, running a process instance and then inspect the current state, and running a process instance using mocked implementations.
6) Configure: There are several parts of Baker that can be configured, including but not limited to: event store connection, clustering, etc.
7) Deploy: Baker has a cluster mode, which must be deployed with a certain order or by configuring service discovery.
8) Monitor: Baker provides event listeners, which will allow you to monitor the process instances.
9) Resolve Failed Processes:
