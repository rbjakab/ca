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

    @Override
    public String toString() {
        return "PathVertex{" + "key=" + key + ", loc=" + loc.getName() +
                ", parentKey=" + parentKey + " parentEdge=" + edgeToString() + '}';
    }

    private String edgeToString() {
        String stringForReturn = "";

        if (parentEdge != null) {
            stringForReturn += "<";
            stringForReturn += "Src: ";
            stringForReturn += parentEdge.getSource().toString();
            stringForReturn += " Trgt: ";
            stringForReturn += parentEdge.getTarget().toString();
            stringForReturn += " Stmt: ";
            stringForReturn += parentEdge.getStmt().toString();
            stringForReturn += ">";
        }

        return stringForReturn;
    }
}