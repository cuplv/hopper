package edu.colorado.thresher.core;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.ipa.callgraph.propagation.*;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.CollectionFilter;
import com.ibm.wala.util.graph.traverse.BFSPathFinder;

import java.util.Collections;
import java.util.List;

public class AndroidLeakClient {
  
  // returns error path without weak refs if one can be found, null otherwise
  public static List<Object> findNewErrorPath(HeapGraphWrapper hg, Object srcKey, Object snkKey, IClassHierarchy cha) {
    boolean foundWeakRef;
    for (;;) {
      foundWeakRef = false;
      BFSPathFinder<Object> bfs = new BFSPathFinder<Object>(hg, srcKey, new CollectionFilter<Object>(Collections.singletonList(snkKey)));
      List<Object> path = bfs.find();
      if (path == null) return null;

      int srcIndex = 1, snkIndex = 0;
      Object fieldKey = null;
      while (srcIndex < path.size()) {
        Object src = path.get(srcIndex);
        if (src instanceof PointerKey && !(src instanceof StaticFieldKey)) {
          // src is intermediate point in points-to edge; either field name or
          // array contents
          if (src instanceof ArrayContentsKey) {
            fieldKey = src;
          } else if (src instanceof InstanceFieldKey) {
            InstanceFieldKey ifk = (InstanceFieldKey) src;
            fieldKey = ifk;
          } 
          srcIndex++;
        } else {
          Object snk = path.get(snkIndex);
          if (isWeakReference(src, snk, cha)) {
            hg.addIgnoreEdge(fieldKey, snk);
            foundWeakRef = true;
            break;
          }
          fieldKey = null;
          snkIndex = srcIndex;
          srcIndex++;
        }
      }
      if (!foundWeakRef) {
        if (Options.SCALA_DEBUG) {
          System.out.println("<FIELD PATH Length: " + path.size());
          for (int i = path.size() - 1; i >= 0; i--)
            System.out.println(path.get(i) + " (" + path.get(i).getClass() + ")");
          System.out.println("</FIELD PATH>");
        }
        return path;
      } // else, try finding another path without weak references
    }
  }
  
  private static IClass WEAK_REFERENCE;
  
  private static boolean isWeakReference(Object src, Object snk, IClassHierarchy cha) {
    if (WEAK_REFERENCE == null) WEAK_REFERENCE = cha.lookupClass(TypeReference.findOrCreate(ClassLoaderReference.Application, "Ljava/lang/ref/WeakReference"));    
    if (!Options.INCLUDE_WEAK_REFERENCES) {
      // check if any links in the path are WeakReference
      if (src instanceof InstanceKey) {
        InstanceKey key = (InstanceKey) src;
        IClass type = key.getConcreteType();
        if (type.equals(WEAK_REFERENCE) || cha.isSubclassOf(type, WEAK_REFERENCE))
          return true;
      }
      if (snk instanceof InstanceKey) {
        InstanceKey key = (InstanceKey) snk;
        IClass type = key.getConcreteType();
        if (type.equals(WEAK_REFERENCE) || cha.isSubclassOf(type, WEAK_REFERENCE))
          return true;
      }
    }
    return false;
  }
}
