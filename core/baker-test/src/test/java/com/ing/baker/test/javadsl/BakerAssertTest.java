package com.ing.baker.test.javadsl;

import akka.actor.ActorSystem;
import com.ing.baker.runtime.akka.AkkaBaker;
import com.ing.baker.runtime.javadsl.Baker;
import com.typesafe.config.ConfigFactory;
import org.junit.Assert;
import org.junit.Test;

import java.util.UUID;

public class BakerAssertTest {

    private final Baker baker = AkkaBaker.java(ConfigFactory.defaultApplication(), ActorSystem.apply("test"));

    private BakerAssert createBakerAssert() {
        String recipeInstanceId = UUID.randomUUID().toString();

        // TODO add recipe


        return BakerAssert.of(baker, recipeInstanceId);
    }

    @Test
    public void test() {
        BakerAssert bakerAssert = createBakerAssert();
        Assert.assertNotNull(bakerAssert);
    }
}
