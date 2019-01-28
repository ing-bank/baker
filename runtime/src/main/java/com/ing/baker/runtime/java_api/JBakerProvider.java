package com.ing.baker.runtime.java_api;

import com.ing.baker.runtime.core.BakerProvider$;

public class JBakerProvider {
    public static JBaker get() {
        return new JBaker(BakerProvider$.MODULE$.get());
    }
}