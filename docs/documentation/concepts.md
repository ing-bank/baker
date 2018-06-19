# Concepts

Baker introduces interactions, ingredients, and events as a model of abstracting. With these three components we can create recipes.

Think about these in the context of a Bakery with a baker using ingeredients to bake a pizza

## Ingredient

Ingredients are like the name implies the  ingredients that the Baker needs to execute the steps in the Recipe.

In our case Ingredients are the data that is needed and created by interactions.

For example to make a money transfer you need to know the IBANs of the two account numbers and the amount of money to be transferred

## Interaction
An interaction can be seen as any action the baker needs fulfil to take to finish his recipe.

Baker is made for complex orchestrations so a interaction is any interaction with an outside system.

An interaction can be a call to internal or external system (can be an API, EMS service, etc.).

The goal of this call is to do work for us for example register a customer, send a present, or transfer money;