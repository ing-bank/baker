package com.ing.baker.recipe;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.ProcessId;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;
import com.ing.baker.recipe.javadsl.InteractionFailureStrategy;
import com.ing.baker.recipe.javadsl.Recipe;

import java.time.Duration;

import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;

public class TestRecipeJava {


  public static class EmptyEvent {}

  public static class InitialEvent {
      private String initialIngredient;

      public InitialEvent(String initialIngredient) {
          this.initialIngredient = initialIngredient;
      }

      public String getInitialIngredient() {
          return initialIngredient;
      }

      public void setInitialIngredient(String initialIngredient) {
          this.initialIngredient = initialIngredient;
      }
  }

    private static final class InteractionOneSuccessful {
    }
    private static class InteractionOne implements Interaction {
        @FiresEvent(oneOf = InteractionOneSuccessful.class)
        InteractionOneSuccessful apply(@ProcessId final String processId,
                                       @RequiresIngredient("initialIngredient") final String initialIngredient) {
            return new InteractionOneSuccessful();
        }
    }

    private static final class EventFromInteractionTwo {
        private String interactionTwoIngredient;

        public EventFromInteractionTwo(String interactionTwoIngredient) {
            this.interactionTwoIngredient = interactionTwoIngredient;
        }

        public String getInteractionTwoIngredient() {
            return interactionTwoIngredient;
        }

        public void setInteractionTwoIngredient(String interactionTwoIngredient) {
            this.interactionTwoIngredient = interactionTwoIngredient;
        }
    }

    private static class InteractionTwo implements Interaction {
        @FiresEvent(oneOf = EventFromInteractionTwo.class)
        EventFromInteractionTwo apply(
                @RequiresIngredient("initialIngredient") final String initialIngredient) {
            return new EventFromInteractionTwo("A");
        }
    }

    private static final class InteractionThreeSuccessful {
        private String interactionThreeIngredientA;
        private String interactionThreeIngredientB;

        public InteractionThreeSuccessful(String interactionThreeIngredientA, String interactionThreeIngredientB) {
            this.interactionThreeIngredientA = interactionThreeIngredientA;
            this.interactionThreeIngredientB = interactionThreeIngredientB;
        }

        public String getInteractionThreeIngredientA() {
            return interactionThreeIngredientA;
        }

        public void setInteractionThreeIngredientA(String interactionThreeIngredientA) {
            this.interactionThreeIngredientA = interactionThreeIngredientA;
        }

        public String getInteractionThreeIngredientB() {
            return interactionThreeIngredientB;
        }

        public void setInteractionThreeIngredientB(String interactionThreeIngredientB) {
            this.interactionThreeIngredientB = interactionThreeIngredientB;
        }
    }

    public static class InteractionThree implements Interaction {
      @FiresEvent(oneOf = InteractionThreeSuccessful.class)
      InteractionThreeSuccessful apply(@RequiresIngredient("interactionTwoIngredient") final String interactionTwoIngredient,
                                       @RequiresIngredient("initialIngredient") final String initialIngredient) {
          return new InteractionThreeSuccessful("A", "B");
      }
    }

    public static final class SupplierInteractionSuccessful {
        String suppliedValue;

        public SupplierInteractionSuccessful(String suppliedValue) {
            this.suppliedValue = suppliedValue;
        }

        public String getSuppliedValue() {
            return suppliedValue;
        }

        public void setSuppliedValue(String suppliedValue) {
            this.suppliedValue = suppliedValue;
        }
    }
    public static class SupplierInteraction implements Interaction {
        @FiresEvent(oneOf = SupplierInteractionSuccessful.class)
        SupplierInteractionSuccessful apply() {
            return new SupplierInteractionSuccessful("supplied");
        }
    }


    public static Recipe getRecipe(String name) {
        return new Recipe(name)
                .withInteractions(
                        of(InteractionOne.class)
                                .withFailureStrategy(new InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder()
                                        .withInitialDelay(Duration.ofMillis(10))
                                        .withMaximumRetries(3)
                                        .build()
                                ),
                        of(InteractionTwo.class),
                        of(SupplierInteraction.class)
                                .withRequiredEvent(EmptyEvent.class),
                        of(InteractionThree.class)
                                .withRequiredEvent(SupplierInteractionSuccessful.class)
                )
                .withSensoryEvent(InitialEvent.class)
                .withSensoryEvent(EmptyEvent.class);
    }
}
