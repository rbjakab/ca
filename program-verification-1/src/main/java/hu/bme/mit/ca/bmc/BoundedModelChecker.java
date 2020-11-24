package hu.bme.mit.ca.bmc;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.sql.SQLOutput;
import java.util.*;
import java.util.concurrent.TimeUnit;
import java.util.Collections;

import com.google.common.base.Stopwatch;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public final class BoundedModelChecker implements SafetyChecker {

	private final CFA cfa;
	private final int bound;
	private final int timeout;

	private BoundedModelChecker(final CFA cfa, final int bound, final int timeout) {
		checkArgument(bound >= 0);
		checkArgument(timeout >= 0);

		this.cfa = checkNotNull(cfa);
		this.bound = bound;
		this.timeout = timeout;
	}

	public static BoundedModelChecker create(final CFA cfa, final int bound, final int timeout) {
		return new BoundedModelChecker(cfa, bound, timeout);
	}

	@Override
	public SafetyResult check() {
		final Stopwatch stopwatch = Stopwatch.createStarted();

		Solver solver = Z3SolverFactory.getInstace().createSolver();

		/*
		{
			System.out.println("-----------------------");

			System.out.println("Locations...");
			System.out.println("- Init location");
			System.out.println("--- " + cfa.getInitLoc().getName());
			System.out.println("- Other locations");
			for (CFA.Loc elem : cfa.getLocs()) {
				String elem_neve = elem.getName();
				if (elem != cfa.getFinalLoc() &&
						elem != cfa.getErrorLoc() &&
						elem != cfa.getInitLoc() &&
						!elem_neve.equals("")) {
					System.out.println("--- " + elem_neve);
				}
			}
			System.out.println("- Final/Error locations");
			System.out.println("--- Final: " + cfa.getFinalLoc().getName());
			System.out.println("--- Error: " + cfa.getErrorLoc().getName());

			System.out.println("\nForward...");
			for (CFA.Loc elem : cfa.getLocs()) {
				String elem_neve = elem.getName();
				if (!elem_neve.equals("")) {
					System.out.print("--- " + elem_neve + ": ");
					for (CFA.Edge el : elem.getOutEdges()) {
						if (!el.getTarget().toString().equals("")) {
							System.out.print(el.getTarget().toString() + " ");
						}
					}
					System.out.print("[" + elem.getOutEdges().size() + "]");
					System.out.println("");
				}
			}

			System.out.println("\nBackward...");
			for (CFA.Loc elem : cfa.getLocs()) {
				String elem_neve = elem.getName();
				if (!elem_neve.equals("")) {
					System.out.print("--- " + elem_neve + ": ");
					for (CFA.Edge el : elem.getInEdges()) {
						if (!el.getSource().toString().equals("")) {
							System.out.print(el.getSource().toString() + " ");
						}
					}
					System.out.print("[" + elem.getInEdges().size() + "]");
					System.out.println("");
				}
			}

			System.out.println("-----------------------");
		}
		 */

		while (stopwatch.elapsed(TimeUnit.SECONDS) < timeout) {

			/* System level variables */
			int depth = 0;
			int availablePaths;

			/* Forward */
			Vector<PathVertex> path = new Vector<>();
			int pathIndex = 0;

			CFA.Loc actLoc = cfa.getInitLoc();
			Queue<PathVertex> queue = new LinkedList<>();
			Queue<PathVertex> queue2 = new LinkedList<>();

			queue.add(new PathVertex(pathIndex, pathIndex, actLoc, null));
			path.add(new PathVertex(pathIndex, pathIndex, actLoc, null));
			pathIndex++;

			/* Backward */
			Vector<PathVertex> pathBW = new Vector<>();

			CFA.Loc errorLoc = cfa.getErrorLoc();
			Queue<PathVertex> queueBW = new LinkedList<>();
			Queue<PathVertex> queue2BW = new LinkedList<>();

			queueBW.add(new PathVertex(queueBW.size(), queueBW.size(), errorLoc, null));
			pathBW.add(new PathVertex(pathBW.size(), pathBW.size(), errorLoc, null));

			/* Loop */
			while (true) {
				depth++;

				availablePaths = 0;

				for (PathVertex item: queue) {
					PathVertex actPV = item;

					for (CFA.Edge edge : actPV.loc.getOutEdges()) {
						CFA.Loc nextLoc = edge.getTarget();
						PathVertex nextPV = new PathVertex(pathIndex, actPV.key, nextLoc, edge);
						pathIndex++;

						path.add(nextPV);

						/* 1 */
						List<Stmt> stmts = getStmtList(getEdgePath(path, true));
						Collection<Expr<BoolType>> exprs = StmtToExprTransformer.unfold(stmts);
						if (isSat(solver, exprs)) {
							queue2.add(nextPV);
							availablePaths++;
						}
					}
				}
				queueTransfer(queue2, queue);

				/* 1 */
				if (availablePaths == 0) {
					System.out.println("SAFE -- 1. depth: " + depth);
					return SafetyResult.UNKNOWN; // TODO
				}

				/* 2 */
				if (!isSatError(queueBW, queue2BW, pathBW, solver, 1)) {
					System.out.println("SAFE -- 2. depth: " + depth);
					return SafetyResult.UNKNOWN; // TODO
				}

				/* 3 */
				for (PathVertex item: queue) {
					if (item.loc == cfa.getErrorLoc()) {

						List<Stmt> stmts = getStmtList(getEdgePathFromElement(path, item, true));
						Collection<Expr<BoolType>> exprs = StmtToExprTransformer.unfold(stmts);

						if (isSat(solver, exprs)) {
							System.out.println("UNSAFE. depth: " + depth);
							return SafetyResult.UNSAFE;
						}
					}
				}
			}
		}

		stopwatch.stop();

		return SafetyResult.TIMEOUT;
	}

	private List<CFA.Edge> getEdgePathFromElement(Vector<PathVertex> path, PathVertex item, boolean reverse) {
		List<CFA.Edge> edgeList = new ArrayList<>();
		PathVertex actPV = item;

		while (actPV.key != 0) {
			edgeList.add(actPV.parentEdge);
			actPV = getParentVertex(path, actPV.parentKey);
		}

		if (reverse) {
			return reverseList(edgeList);
		} else {
			return edgeList;
		}
	}

	private List<CFA.Edge> getEdgePath(Vector<PathVertex> path, boolean reverse) {
		List<CFA.Edge> edgeList = new ArrayList<>();
		PathVertex actPV = path.lastElement();

		while (actPV.key != 0) {
			edgeList.add(actPV.parentEdge);
			actPV = getParentVertex(path, actPV.parentKey);
		}

		if (reverse) {
			return reverseList(edgeList);
		} else {
			return edgeList;
		}
	}

	private List<CFA.Edge> getEdgePathReversedFromElement(Vector<PathVertex> path, boolean reverse) {
		List<CFA.Edge> edgeList = new ArrayList<>();
		PathVertex actPV = path.lastElement();

		while (actPV.key != 0) {
			edgeList.add(actPV.parentEdge);
			actPV = getParentVertex(path, actPV.parentKey);
		}

		if (reverse) {
			return reverseList(edgeList);
		} else {
			return edgeList;
		}
	}

	private PathVertex getParentVertex(Vector<PathVertex> path, int key) {
		for (int i = 0; i < path.size(); i++) {
			if (path.get(i).key == key) {
				return path.get(i);
			}
		}
		return null;
	}

	private List<Stmt> getStmtList(List<CFA.Edge> edgePath) {
		List<Stmt> stmtList = new ArrayList<>();

		for (int i = 0; i < edgePath.size(); i++) {
			stmtList.add(edgePath.get(i).getStmt());
		}

		return stmtList;
	}

	private List<CFA.Edge> reverseList(List<CFA.Edge> edgeList) {
		List<CFA.Edge> reversedEdgeList = new ArrayList<>();

		for (int i = edgeList.size() - 1; i >= 0; i--) {
			reversedEdgeList.add(edgeList.get(i));
		}

		return reversedEdgeList;
	}

	private int getPathDepth(Vector<PathVertex> path) {
		int depth = 0;

		PathVertex actPV = path.lastElement();

		while (actPV.key != 0) {
			if (!actPV.loc.getName().equals("")) {
				depth++;
			}
			actPV = getParentVertex(path, actPV.parentKey);
		}

		return depth;
	}

	private void writeOutPath(Vector<PathVertex> path, PathVertex item) {
		PathVertex actPV = item;
		List<String> pathListForWritingOut = new ArrayList<String>();

		while (actPV.key != 0) {
			if (actPV.loc.getName().length() != 0) {
				pathListForWritingOut.add(actPV.loc.getName());
			}
			actPV = getParentVertex(path, actPV.parentKey);
		}
		pathListForWritingOut.add(actPV.loc.getName());
		for (int idx = pathListForWritingOut.size() - 1; idx >= 0; idx--) {
			System.out.print(pathListForWritingOut.get(idx));
			if (idx != 0) {
				System.out.print(" -> ");
			}
		}
		System.out.println();
	}

	private void writeOutPathBW(Vector<PathVertex> path, PathVertex item) {
		PathVertex actPV = item;
		List<String> pathListForWritingOut = new ArrayList<String>();

		while (actPV.key != 0) {
			if (actPV.loc.getName().length() != 0) {
				pathListForWritingOut.add(actPV.loc.getName());
			}
			actPV = getParentVertex(path, actPV.parentKey);
		}
		pathListForWritingOut.add(actPV.loc.getName());
		for (int idx = pathListForWritingOut.size() - 1; idx >= 0; idx--) {
			System.out.print(pathListForWritingOut.get(idx));
			if (idx != 0) {
				System.out.print(" -> ");
			}
		}
		System.out.println();
	}

	private void writeOutPathTree(Vector<PathVertex> path) {
		int path_size_max = 100;
		if (path.size() < path_size_max) {
			path_size_max = path.size();
		}
		for (int i = 0; i < path_size_max; i++) {
			System.out.print("key: " + path.get(i).key + " ");
			if (path.get(i).loc.getName().equals("")) {
				System.out.print("loc name: XX ");
			} else {
				System.out.print("loc name: " + path.get(i).loc.getName() + " ");
			}
			if (path.get(i).parentEdge != null) {
				if (path.get(i).parentEdge.getSource().getName().equals("")) {
					System.out.print("parent loc name: XX ");
				} else {
					System.out.print("parent loc name: " + path.get(i).parentEdge.getSource().getName() + " ");
				}
			} else {
				System.out.print("parent loc name: NULL ");
			}
			System.out.print("parent key: " + path.get(i).parentKey + "\n");
		}
	}

	private void queueTransfer(Queue<PathVertex> copyOne, Queue<PathVertex> pasteOne) {
		pasteOne.clear();

		for (PathVertex item: copyOne) {
			pasteOne.add(item);
		}

		copyOne.clear();
	}

	private boolean isSat(Solver solver, Collection<Expr<BoolType>> exprs) {
		boolean status;

		solver.push();
		solver.add(exprs);
		solver.check();

		status = solver.getStatus().isSat();

		solver.pop();

		return status;
	}

	private boolean isSatError(Queue<PathVertex> queueBW, Queue<PathVertex> queue2BW, Vector<PathVertex> pathBW, Solver solver, int numberOfSteps) {
		int availablePaths = 0;

		for (int i = 0; i < numberOfSteps; i++) {
			for (PathVertex item: queueBW) {
				PathVertex actPV = item;

				for (CFA.Edge edge : actPV.loc.getInEdges()) {
					CFA.Loc nextLoc = edge.getSource();
					PathVertex nextPV = new PathVertex(pathBW.size(), actPV.key, nextLoc, edge);

					pathBW.add(nextPV);

					List<Stmt> stmts = getStmtList(getEdgePathReversedFromElement(pathBW, false));
					Collection<Expr<BoolType>> exprs = StmtToExprTransformer.unfold(stmts);
					if (isSat(solver, exprs)) {
						queue2BW.add(nextPV);
						availablePaths++;
					}
				}
			}
			queueTransfer(queue2BW, queueBW);
		}

		if (availablePaths == 0) {
			return false;
		} else {
			for (PathVertex item: queueBW) {
				if (item.loc == cfa.getInitLoc()) {

					List<Stmt> stmts = getStmtList(getEdgePathFromElement(pathBW, item, true));
					Collection<Expr<BoolType>> exprs = StmtToExprTransformer.unfold(stmts);

					if (isSat(solver, exprs)) {
						writeOutPath(pathBW, item);
						return false;
					}
				}
			}
			return true;
		}
	}
}
