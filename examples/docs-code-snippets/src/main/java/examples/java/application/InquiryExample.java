package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;

public class InquiryExample {

    private final Baker baker;

    public InquiryExample(Baker baker) {
        this.baker = baker;
    }

    public void example(String recipeInstanceId) {
        var ingredient = baker.getIngredient(recipeInstanceId, "orderId").join();

        var ingredients = baker.getIngredients(recipeInstanceId).join();

        var events = baker.getEvents(recipeInstanceId).join();

        var eventNames = baker.getEventNames(recipeInstanceId).join();

        var recipeInstanceState = baker.getRecipeInstanceState(recipeInstanceId).join();
    }
}
