package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common.FiresOneOfEvents

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
      inputIngredients = order,
      output = FiresOneOfEvents(valid, sorry))

    val manufactureGoods = Interaction(
      name = "ManufactureGoods",
      inputIngredients = order,
      output = FiresOneOfEvents(goodsManufactured))

    val sendInvoice = Interaction(
      name = "SendInvoice",
      inputIngredients = customerInfo,
      output = FiresOneOfEvents(invoiceWasSent))

    val shipGoods = Interaction(
      name = "ShipGoods",
      inputIngredients = Ingredients(goods, customerInfo),
      output = FiresOneOfEvents(goodsShipped)
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
      output = FiresOneOfEvents(getAccountSuccessful, getAccountFailed)
    )

    val assignAccount = Interaction(
      name = "AssignAccount",
      inputIngredients = Seq(customerId, iban),
      output = FiresOneOfEvents(assignAccountSuccessful, assignAccountFailed)
    )

    val registerIndividual = Interaction(
      name = "RegisterIndividual",
      inputIngredients = Seq(name, address),
      output = FiresOneOfEvents(registerIndividualSuccessful, registerIndividualFailed)
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
}

