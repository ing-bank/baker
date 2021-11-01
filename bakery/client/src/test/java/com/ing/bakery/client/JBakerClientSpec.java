package com.ing.bakery.client;

import com.google.common.collect.ImmutableList;
import com.ing.baker.runtime.javadsl.Baker;
import com.ing.bakery.javadsl.BakerClient;

import java.util.Optional;
import java.util.concurrent.ExecutionException;

public class JBakerClientSpec {

    public void shouldCompileTheRecipeWithoutIssues() throws ExecutionException, InterruptedException {
        Baker baker = BakerClient.build(
                ImmutableList.of("bakeryhost1"),
                "/api/bakery",
                ImmutableList.of(),
                "",
                ImmutableList.of(),
                Optional.empty(),
                true).get();
    }
}
