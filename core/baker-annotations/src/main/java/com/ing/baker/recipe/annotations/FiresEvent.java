package com.ing.baker.recipe.annotations;

import javax.inject.Qualifier;
import java.lang.annotation.*;

/**
 * Annotation for an interaction to show what events can fired from this interaction
 */
@Qualifier
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
public @interface FiresEvent {
    Class<?>[] oneOf();
}
