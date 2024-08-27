package examples.java.events;

import examples.java.ingredients.Address;

import java.util.List;

public record OrderPlaced(
    String orderId,
    String customerId,
    Address address,
    List<String> productIds
) { }
