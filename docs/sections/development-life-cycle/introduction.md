# Introduction

The "Development Life Cycle" serves as a "hands-on" tutorial of Baker. In this tutorial you will build a simple web-shop 
recipe one step at a time. In other words, it's a practical approach to learning Baker.

## Setting the stage
To be practical, we need some kind of context in which we can be practical. To that end, imagine you are working
as a software engineer for a modern e-commerce company. They are building a web-shop made up of different microservices. 
You are responsible for building the order reservation process. The requirements read:

> An `order` consists of an `orderId` and a list of `productIds`. After placing an order we need to verify if the
> warehouse has sufficient stock. We can do this by calling the warehouse service with the `orderId` and `ProductIds`.
> If all products are in stock, the warehouse service returns the ids of the reserved items. If (at least) one of the
> items isn't in stock, the warehouse service returns a list of the unavailable items. If there are unavailable items
> the process should stop.

Evaluating business requirements is always the first step towards creating a Baker process. In the next section you
will learn how to translate these requirements to a Baker recipe.
