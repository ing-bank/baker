package com.ing.baker;

import akka.actor.ActorSystem;
import com.google.common.collect.ImmutableList;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RecipeInstanceId;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;
import com.ing.baker.recipe.javadsl.InteractionFailureStrategy;
import com.ing.baker.recipe.javadsl.Recipe;
import com.ing.baker.runtime.akka.AkkaBaker;
import com.ing.baker.runtime.javadsl.Baker;
import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;

import java.time.Duration;
import java.util.concurrent.ExecutionException;

import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;
import static org.mockito.Matchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

public class Webshop {

    public static class CustomerInfo {
        public final String name;
        public final String address;
        public final String email;

        public CustomerInfo(String name, String address, String email) {
            this.name = name;
            this.address = address;
            this.email = email;
        }
    }

    public static class OrderPlaced {
        public final String order;

        public OrderPlaced(String order) {
            this.order = order;
        }
    }

    public static class CustomerInfoReceived {
        public final CustomerInfo customerInfo;

        public CustomerInfoReceived(CustomerInfo customerInfo) {
            this.customerInfo = customerInfo;
        }
    }

    public interface ValidateOrder extends Interaction {

        interface Outcome {
        }

        class Failed implements Outcome {
        }

        class Valid implements Outcome {
        }

        @FiresEvent(oneOf = {Failed.class, Valid.class})
        Outcome apply(@RecipeInstanceId String recipeInstanceId, @RequiresIngredient("order") String key);
    }

    public interface ManufactureGoods extends Interaction {
        class GoodsManufactured {
            public final String goods;

            public GoodsManufactured(String goods) {
                this.goods = goods;
            }
        }

        @FiresEvent(oneOf = {GoodsManufactured.class})
        GoodsManufactured apply(@RequiresIngredient("order") String order);
    }

    public interface SendInvoice extends Interaction {

        class InvoiceWasSent {
        }

        @FiresEvent(oneOf = {InvoiceWasSent.class})
        InvoiceWasSent apply(@RequiresIngredient("customerInfo") CustomerInfo customerInfo);
    }

    public interface ShipGoods extends Interaction {

        class GoodsShipped {
            public final String trackingId;

            public GoodsShipped(String trackingId) {
                this.trackingId = trackingId;
            }
        }

        @FiresEvent(oneOf = {GoodsShipped.class})
        GoodsShipped apply(@RequiresIngredient("goods") String goods, @RequiresIngredient("customerInfo") CustomerInfo customerInfo);
    }

    public static class PaymentMade {
    }

    public final static Recipe webshopRecipe = new Recipe("webshop")
            .withSensoryEvents(
                    OrderPlaced.class,
                    CustomerInfoReceived.class,
                    PaymentMade.class)
            .withInteractions(
                    of(ValidateOrder.class),
                    of(ManufactureGoods.class)
                            .withRequiredEvents(PaymentMade.class, ValidateOrder.Valid.class),
                    of(SendInvoice.class)
                            .withRequiredEvents(ShipGoods.GoodsShipped.class),
                    of(ShipGoods.class))
            .withDefaultFailureStrategy(
                    new InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder()
                            .withInitialDelay(Duration.ofMillis(100))
                            .withDeadline(Duration.ofHours(24))
                            .withMaxTimeBetweenRetries(Duration.ofMinutes(10))
                            .build());

    ShipGoods shipGoodsMock = mock(ShipGoods.class);
    SendInvoice sendInvoiceMock = mock(SendInvoice.class);
    ManufactureGoods manufactureGoodsMock = mock(ManufactureGoods.class);
    ValidateOrder validateOrderMock = mock(ValidateOrder.class);


    //    @Test
    public void testWebshop() throws ExecutionException, InterruptedException {

        Config config = ConfigFactory.load("cassandra.conf");

        CompiledRecipe recipe = RecipeCompiler.compileRecipe(webshopRecipe);

        System.out.println(recipe.getRecipeVisualization());

        // test data
        CustomerInfo customerInfo = new CustomerInfo("klaas", "straat", "email");
        String order = "123";

        // prepare mocks
        when(shipGoodsMock.apply(any(), any())).thenReturn(new ShipGoods.GoodsShipped("trackingId"));
        when(sendInvoiceMock.apply(any())).thenReturn(new SendInvoice.InvoiceWasSent());
        when(manufactureGoodsMock.apply(any())).thenReturn(new ManufactureGoods.GoodsManufactured("goods"));
        when(validateOrderMock.apply(any(), any())).thenReturn(new ValidateOrder.Valid());

        ActorSystem system = ActorSystem.create("webshop");
        Baker baker = AkkaBaker.java(config, system);

        baker.addInteractionInstances(ImmutableList.of(shipGoodsMock, sendInvoiceMock, manufactureGoodsMock, validateOrderMock));

        String recipeId = baker.addRecipe(recipe).get();

        String recipeInstanceId = "56a70f82-a24d-497f-b3ac-57366adbb39c"; //UUID.randomUUID().toString();

        System.out.println("recipeId: " + recipeId);
        System.out.println("RecipeInstanceId: " + recipeInstanceId);


//        baker.bake(recipeId, RecipeInstanceId);
//
//        baker.processEvent(RecipeInstanceId, new CustomerInfoReceived(customerInfo));
//        baker.processEvent(RecipeInstanceId, new OrderPlaced(order));
//        baker.processEvent(RecipeInstanceId, new PaymentMade());

//        System.out.println("ingredients: " + baker.getIngredients(RecipeInstanceId).toString());
//        System.out.println("events: " + baker.getProcessState(RecipeInstanceId)
//                .thenApply(ProcessState::events).get().toString());
    }
}
