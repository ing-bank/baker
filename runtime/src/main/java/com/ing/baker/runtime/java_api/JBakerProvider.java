package com.ing.baker.runtime.java_api;

import com.ing.baker.runtime.JBaker;
import com.ing.baker.runtime.core.BakerProvider$;
import com.typesafe.config.Config;

public class JBakerProvider {
    public static JBaker get() {
        return new JBaker(BakerProvider$.MODULE$.get());
    }
    public static JBaker get(Config config) {
        return new JBaker(config);
    }

}