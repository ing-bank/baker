package examples.java.events;

import java.util.List;

public record OrderPlaced(
        String orderId,
        List<String> productIds
) { }
