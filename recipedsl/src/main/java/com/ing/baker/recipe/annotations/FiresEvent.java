package com.ing.baker.recipe.annotations;

import com.ing.baker.recipe.javadsl.Event;

import javax.inject.Qualifier;
import java.lang.annotation.*;

@Qualifier
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
public @interface FiresEvent {
    Class<Event>[] oneOf();
}
