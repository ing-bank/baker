package com.ing.baker.test.javadsl.recipe;

import java.util.List;

    public class OrderPlaced {
        private final String orderId;
        private final List<String> items;

        public OrderPlaced(String orderId, List<String> items) {
            this.orderId = orderId;
            this.items = items;
        }

        public List<String> getItems() {
            return items;
        }

        public String getOrderId() {
            return orderId;
        }
    }

