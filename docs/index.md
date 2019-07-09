## Introduction

Upgrading your business to an agile, adaptive and scalable microservice based architecture does bring significant advantages, 
but also critical challenges that must be resolved, namely the coupling of business logic to service 
technologies and the inherent complexities of distributed systems. Baker solves these challenges by providing an expressive 
language to encode your business logic _(recipe)_, and a distributed runtime to scale _recipe instances_ with little 
configuration and no extra development. 

**Decouple your business logic from your microservices**: When developing microservices it is easy to fall into bad practices 
where developers encode essential business logic into code polluted with implementation details, and even worse, distributed 
over many independent projects/repositories. Baker, in contrast, requires the developer to _express the business logic as a 
Recipe_ by using the provided language DSL, and separately _code implementations of the data (events) and the process steps 
(interactions)_, enforcing decoupling of business from technology.

**Ease the friction of distributed systems**: When developing microservices you are confronted with all the inherent 
challenges of distributed systems, topics like communication models, consistency decisions, handling failure, scaling 
models, etc. Baker eases the development by providing out-of-the-box solutions in its clusterized runtime. Baker nodes 
are able to create and distribute _recipe instances_ between them, handle _failed interactions_ with several strategies, 
restore the state of long-lived process and more, allowing the developer to focus on what it matters for the business.

**Reason about your business without the burdens of technology**: Baker can _visualize your recipes_, enabling developers 
and business stakeholders to better communicate and reason about the business processes.

Example of a simple web shop recipe:

![](images/webshop.svg)
