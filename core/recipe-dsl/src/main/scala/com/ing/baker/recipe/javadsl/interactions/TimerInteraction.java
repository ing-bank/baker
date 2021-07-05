package com.ing.baker.recipe.javadsl.interactions;

        import com.ing.baker.recipe.annotations.FiresEvent;
        import com.ing.baker.recipe.annotations.RequiresIngredient;
        import com.ing.baker.recipe.javadsl.Interaction;

        import java.time.Duration;

public interface TimerInteraction extends Interaction {
    @FiresEvent(oneOf = TimeWaited.class)
    public TimeWaited apply(@RequiresIngredient("WaitTime") Duration WaitTime);
}