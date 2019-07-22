package webshop;

import akka.actor.ActorSystem;
import akka.stream.ActorMaterializer;
import akka.stream.Materializer;
import com.ing.baker.runtime.javadsl.Baker;
import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;


public class JTmp {

    static void run() {

        ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
        Materializer materializer = ActorMaterializer.create(actorSystem);
        Config config = ConfigFactory.load();

        Baker baker = Baker.akka(config, actorSystem, materializer);

    }
}
