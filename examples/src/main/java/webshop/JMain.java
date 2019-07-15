package webshop;

import akka.actor.ActorSystem;
import akka.stream.ActorMaterializer;
import akka.stream.Materializer;
import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import com.ing.baker.runtime.javadsl.EventResult;

import java.util.concurrent.CompletableFuture;

public class JMain {

    static public void main(String[] args) {

        ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
        Materializer materializer = ActorMaterializer.create(actorSystem);
        Baker baker = Baker.akkaLocalDefault(actorSystem, materializer);

        String recipeInstanceId = "recipe id from previously baked recipe instance";
        String[] items = {"item1", "item2"};
        EventInstance firstOrderPlaced =
                EventInstance.from(new JWebshopRecipe.OrderPlaced("order-uuid", items));

        CompletableFuture<EventResult> result = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced);
    }
}
