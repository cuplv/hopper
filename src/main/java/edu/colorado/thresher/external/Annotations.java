package edu.colorado.thresher.external;

import java.lang.annotation.*;

public class Annotations {
  
  /**
   * Annotating a class with noStaticRef indicates that the class is transient
   * and should not be referenced (directly or indirectly) by a static field,
   * as this might preclude garbage collection
   */
  @Retention(RetentionPolicy.RUNTIME)
  public static @interface noStaticRef {}
  
}
