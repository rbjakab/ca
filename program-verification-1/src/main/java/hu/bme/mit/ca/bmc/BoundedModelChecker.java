package hu.bme.mit.ca.bmc;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.*;
import java.util.concurrent.TimeUnit;

import com.google.common.base.Stopwatch;

import hu.bme.mit.theta.cfa.CFA;
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

			CFA.Loc actLoc = cfa.getInitLoc();
			Queue<PathVertex> queue = new LinkedList<>();
			Queue<PathVertex> queue2 = new LinkedList<>();

			queue.add(new PathVertex(0, 0, actLoc, null));
			path.add(new PathVertex(0, 0, actLoc, null));

			/* Backward */
			Vector<PathVertex> pathBW = new Vector<>();

			CFA.Loc errorLoc = cfa.getErrorLoc();
			Queue<PathVertex> queueBW = new LinkedList<>();
			Queue<PathVertex> queue2BW = new LinkedList<>();

			queueBW.add(new PathVertex(0, 0, errorLoc, null));
			pathBW.add(new PathVertex(0, 0, errorLoc, null));

			/* Loop */
			while (true) {
				depth++;

				availablePaths = 0;

				for (PathVertex item: queue) {
					for (CFA.Edge edge : item.loc.getOutEdges()) {
						CFA.Loc nextLoc = edge.getTarget();
						PathVertex nextPV = new PathVertex(path.size(), item.key, nextLoc, edge);

						path.add(nextPV); // TODO: in the future it shall be inside of the if

						/* 1 */
						List<Stmt> stmts = getStmtList(getEdgePathFromElement(path, path.lastElement(),true));
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
					return SafetyResult.UNKNOWN; // TODO: change it to SAFE
				}

				/* 2 */
				if (!isSatError(queueBW, queue2BW, pathBW, solver)) {
					System.out.println("SAFE -- 2. depth: " + depth);
					return SafetyResult.UNKNOWN; // TODO: change it to SAFE
				}

				/* 3 */
				for (PathVertex item: queue) {
					if (item.loc == cfa.getErrorLoc()) {

						List<Stmt> stmts = getStmtList(getEdgePathFromElement(path, item, true));
						Collection<Expr<BoolType>> exprs = StmtToExprTransformer.unfold(stmts);

						if (isSat(solver, exprs)) {
							System.out.println("UNSAFE. depth: " + depth);
							writeOutPath(path, item);
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
			actPV = path.get(actPV.parentKey);
		}

		if (reverse) {
			return reverseList(edgeList);
		} else {
			return edgeList;
		}
	}

	private List<Stmt> getStmtList(List<CFA.Edge> edgePath) {
		List<Stmt> stmtList = new ArrayList<>();

		for (CFA.Edge edge : edgePath) {
			stmtList.add(edge.getStmt());
		}

		return stmtList;
	}

	// TODO: more efficient way to reverse the list
	private List<CFA.Edge> reverseList(List<CFA.Edge> edgeList) {
		List<CFA.Edge> reversedEdgeList = new ArrayList<>();

		for (int i = edgeList.size() - 1; i >= 0; i--) {
			reversedEdgeList.add(edgeList.get(i));
		}

		return reversedEdgeList;
	}

	private void writeOutPath(Vector<PathVertex> path, PathVertex item) {
		PathVertex actPV = item;
		List<String> pathListForWritingOut = new ArrayList<>();

		while (actPV.key != 0) {
			if (actPV.loc.getName().length() != 0) {
				pathListForWritingOut.add(actPV.loc.getName());
			}
			actPV = path.get(actPV.parentKey);
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

	/* private void writeOutPathTree(Vector<PathVertex> path) {
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
	} */

	private void queueTransfer(Queue<PathVertex> copyOne, Queue<PathVertex> pasteOne) {
		pasteOne.clear();
		pasteOne.addAll(copyOne);
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

	private boolean isSatError(Queue<PathVertex> queueBW, Queue<PathVertex> queue2BW, Vector<PathVertex> pathBW, Solver solver) {
		int availablePaths = 0;

		for (PathVertex item: queueBW) {
			for (CFA.Edge edge : item.loc.getInEdges()) {
				CFA.Loc nextLoc = edge.getSource();
				PathVertex nextPV = new PathVertex(pathBW.size(), item.key, nextLoc, edge);

				pathBW.add(nextPV);

				List<Stmt> stmts = getStmtList(getEdgePathFromElement(pathBW, pathBW.lastElement(), false));
				Collection<Expr<BoolType>> exprs = StmtToExprTransformer.unfold(stmts);
				if (isSat(solver, exprs)) {
					queue2BW.add(nextPV);
					availablePaths++;
				}
			}
		}
		queueTransfer(queue2BW, queueBW);

		return availablePaths != 0;
	}
}
