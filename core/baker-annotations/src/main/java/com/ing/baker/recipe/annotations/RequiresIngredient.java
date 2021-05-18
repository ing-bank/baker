package com.ing.baker.recipe.annotations;

import javax.inject.Qualifier;
import java.lang.annotation.*;

/**
 * An annotation to be added to an argument of an interaction to show what ingredient should be used here.
 */
@Qualifier
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.PARAMETER)
public @interface RequiresIngredient {
    String value() default "";
}
