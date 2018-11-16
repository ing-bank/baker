package com.ing.baker.recipe.scaladsl

object Examples {

  object webshop {

    case class CustomerInfo(name: String, address: String, email: String)

    // ingredients

    val customerInfo = Ingredient[CustomerInfo]("customerInfo")
    val goods = Ingredient[String]("goods")
    val trackingId = Ingredient[String]("trackingId")
    val order = Ingredient[String]("order")
    val name = Ingredient[String]("name")
    val address = Ingredient[String]("address")
    val email = Ingredient[String]("email")

    // events

    val goodsShipped = Event("GoodsShipped", trackingId)
    val orderPlaced = Event("OrderPlaced", order)
    val customer = Event("Customer", name, address, email)
    val customerInfoReceived = Event("CustomerInfoReceived", customerInfo)
    val paymentMade = Event("PaymentMade")
    val valid = Event("Valid")
    val sorry = Event("Sorry")
    val goodsManufactured = Event("GoodsManufactured", goods)
    val invoiceWasSent = Event("InvoiceWasSent")

    // interactions

    val validateOrder = Interaction(
      name = "ValidateOrder",
      inputIngredients = Seq(order),
      output = Seq(valid, sorry))

    val manufactureGoods = Interaction(
      name = "ManufactureGoods",
      inputIngredients = Seq(order),
      output = Seq(goodsManufactured))

    val sendInvoice = Interaction(
      name = "SendInvoice",
      inputIngredients = Seq(customerInfo),
      output = Seq(invoiceWasSent))

    val shipGoods = Interaction(
      name = "ShipGoods",
      inputIngredients = Seq(goods, customerInfo),
      output = Seq(goodsShipped)
    )

    // recipe

    val webShopRecipe: Recipe =
      Recipe("WebShop")
        .withInteractions(
          validateOrder,
          manufactureGoods
            .withRequiredEvents(valid, paymentMade),
          shipGoods,
          sendInvoice
            .withRequiredEvent(goodsShipped)
        )
        .withSensoryEvents(
          customerInfoReceived,
          orderPlaced,
          paymentMade)
  }

  object open_account {

    // ingredients

    val iban = Ingredient[String]("iban")
    val name = Ingredient[String]("name")
    val address = Ingredient[String]("address")
    val customerId = Ingredient[String]("customerId")

    val getAccountFailedReason = Ingredient[String]("getAccountFailedReason")
    val registerIndividualFailedReason = Ingredient[String]("registerIndividualFailedReason")
    val assignAccountFailedReason = Ingredient[String]("registerIndividualFailedReason")

    // events

    val getAccountSuccessful = Event("GetAccountSuccessful", iban)
    val getAccountFailed = Event("GetAccountFailed", getAccountFailedReason)

    val assignAccountSuccessful = Event("AssignAccountSuccessful")
    val assignAccountFailed = Event("AssignAccountFailed", assignAccountFailedReason)

    val registerIndividualSuccessful = Event("RegisterIndividualSuccessful", customerId)
    val registerIndividualFailed = Event("RegisterIndividualFailed", registerIndividualFailedReason)

    val termsAndConditionsAccepted = Event("TermsAndConditionsAccepted")
    val individualInformationSubmitted = Event("individualInformationSubmitted", name, address)

    // interactions

    val getAccount = Interaction(
      name = "GetAccount",
      inputIngredients = Seq.empty,
      output = Seq(getAccountSuccessful, getAccountFailed)
    )

    val assignAccount = Interaction(
      name = "AssignAccount",
      inputIngredients = Seq(customerId, iban),
      output = Seq(assignAccountSuccessful, assignAccountFailed)
    )

    val registerIndividual = Interaction(
      name = "RegisterIndividual",
      inputIngredients = Seq(name, address),
      output = Seq(registerIndividualSuccessful, registerIndividualFailed)
    )

    // recipe

    val openAccountRecipe = Recipe("OpenAccountRecipe")
      .withInteractions(
        assignAccount,
        getAccount.withRequiredEvent(termsAndConditionsAccepted),
        registerIndividual)
      .withSensoryEvents(
        termsAndConditionsAccepted,
        individualInformationSubmitted)
  }

  object onboarding {

    //Ingredients
    val customerName = Ingredient[String]("customerName")
    val customerId = Ingredient[String]("customerId")
    val accountId = Ingredient[Integer]("accountId")
    val accountName = Ingredient[Integer]("accountName")

    //Events
    val agreementsAcceptedEvent = Event("agreementsAccepted")
    val manualApprovedEvent = Event("manualApproved")
    val automaticApprovedEvent = Event("automaticApproved")
    val NameProvidedEvent = Event("nameProvided", customerName)
    val accountOpenedEvent = Event("accountOpened", accountId, accountName)
    val accountOpenedFailedEvent = Event("accountOpenedFailed")
    val createCustomerSuccessful = Event("CreateCustomerSuccessful", customerId)

    //Recipe
    //Interactions
    val createCustomer = Interaction(
      name = "CreateCustomer",
      inputIngredients = Seq(customerName),
      output = Seq(createCustomerSuccessful)
    )

    val openAccount = Interaction(
      name = "OpenAccount",
      inputIngredients =Seq(customerId),
      output = Seq(accountOpenedEvent, accountOpenedFailedEvent))

    val onboardingRecipe: Recipe =
      Recipe("newCustomerRecipe")
        .withInteractions(
          createCustomer
            .withRequiredEvent(
              agreementsAcceptedEvent)
            .withRequiredOneOfEvents(
              automaticApprovedEvent,
              manualApprovedEvent),
          openAccount
            .withEventOutputTransformer(
              accountOpenedEvent,
              "newAccountOpenedEvent",
              Map.empty)
        )
        .withSensoryEvents(
          agreementsAcceptedEvent,
          NameProvidedEvent,
          manualApprovedEvent,
          automaticApprovedEvent
        )
  }
}

