package com.ing.baker.recipe.annotations;

import javax.inject.Qualifier;
import java.lang.annotation.*;

@Qualifier
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
public @interface ProvidesIngredient {
    String value() default "";
}
