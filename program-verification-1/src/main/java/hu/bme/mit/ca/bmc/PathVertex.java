package hu.bme.mit.ca.bmc;

import hu.bme.mit.theta.cfa.CFA;

public class PathVertex {
    int key;
    int parentKey;
    CFA.Loc loc;
    CFA.Edge parentEdge;

    PathVertex(int key, int parentKey, CFA.Loc loc, CFA.Edge parentEdge) {
        this.key = key;
        this.parentKey = parentKey;
        this.loc = loc;
        this.parentEdge = parentEdge;
    }
}