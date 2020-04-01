package com.ing.baker.kafkalistener;

import com.ing.baker.runtime.common.BakerEvent;
import com.ing.baker.runtime.common.EventInstance;

public class ExampleEventProcessor implements EventProcessor {

  @Override
  public void bakerEvent(BakerEvent event) {
    System.out.println("Baker event: " + event.toString());
  }

  @Override
  public void recipeEvent(EventInstance event) {
    System.out.println("Recipe event: " + event.toString());
  }

  public void parseFailure(String serialized, String errorMessage) {
    System.out.println(serialized + " can't be parsed: " + errorMessage);
  }

}
